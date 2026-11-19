import streamlit as st
import psycopg2
from psycopg2.extras import RealDictCursor
from psycopg2 import errors
import requests
import pandas as pd
import hashlib
import hmac
import secrets
import time
from contextlib import contextmanager
from datetime import datetime, date, timedelta

# ============================================================
# MASTER APP: FOOD + EXERCISE + WEIGHT TRACKER
# Includes date-to-date copying of food and exercise entries,
# protein / fat / carbohydrate tracking for food, and import of
# macros from older food_entries columns.
# Sections are shown as selectable tabs.
# Manual food can be entered per 100 g OR as actual calories.
# Run: streamlit run master.py
# ============================================================

st.set_page_config(
    page_title="My Calorie & Exercise Tracker",
    page_icon="🥗",
    layout="wide"
)

USDA_API_URL = "https://api.nal.usda.gov/fdc/v1/foods/search"
NINJAS_EXERCISES_URL = "https://api.api-ninjas.com/v1/exercises"
NINJAS_CALORIES_URL = "https://api.api-ninjas.com/v1/caloriesburned"

# Quantity type label used for manually entered "actual calories" entries.
ACTUAL_CAL_TYPE = "Actual calories"

# Set to True if your OLD macro columns hold values per 100 g.
# Leave False if they hold the total grams for the logged quantity.
# (Old columns with "100" in the name are always treated as per 100 g.)
LEGACY_MACROS_ARE_PER_100G = False

LEGACY_MACRO_NAMES = {
    "protein": ["protein", "proteins", "protein_100g", "protein_grams"],
    "fat": ["fat", "fats", "total_fat", "fat_100g", "fat_grams"],
    "carbs": ["carbs", "carb", "carbohydrate", "carbohydrates",
              "carbs_100g", "carbohydrates_100g", "carbs_grams"],
}


# ============================================================
# DATABASE CONNECTION
# Uses exactly the same [postgres] Streamlit secrets as app.py.
# ============================================================
@contextmanager
def get_connection():
    conn = psycopg2.connect(
        host=st.secrets["postgres"]["host"],
        port=int(st.secrets["postgres"].get("port", 5432)),
        dbname=st.secrets["postgres"].get("database", "postgres"),
        user=st.secrets["postgres"]["user"],
        password=st.secrets["postgres"]["password"],
        sslmode="require",
        connect_timeout=15,
        cursor_factory=RealDictCursor,
    )
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def migrate_exercise_table(cur):
    """
    Bring a pre-existing exercise_entries table (created by an older version
    of the app with a different layout) up to the current schema.
    CREATE TABLE IF NOT EXISTS never alters an existing table, so missing
    columns must be added explicitly.
    """
    cur.execute("""
        SELECT column_name, data_type, is_nullable
        FROM information_schema.columns
        WHERE table_schema = current_schema()
          AND table_name = 'exercise_entries'
    """)
    existing = {r["column_name"]: r for r in cur.fetchall()}
    if not existing:
        return

    required_columns = {
        "exercise_name": "TEXT NOT NULL DEFAULT ''",
        "category": "TEXT NOT NULL DEFAULT 'Other'",
        "duration_minutes": "DOUBLE PRECISION NOT NULL DEFAULT 0",
        "body_weight_kg": "DOUBLE PRECISION NOT NULL DEFAULT 0",
        "lifted_weight_kg": "DOUBLE PRECISION NOT NULL DEFAULT 0",
        "sets": "INTEGER NOT NULL DEFAULT 0",
        "reps": "INTEGER NOT NULL DEFAULT 0",
        "calories_burned": "DOUBLE PRECISION NOT NULL DEFAULT 0",
        "source": "TEXT NOT NULL DEFAULT 'API Ninjas'",
        "entry_date": (
            "TEXT NOT NULL DEFAULT "
            "(to_char(now(), 'YYYY-MM-DD\"T\"HH24:MI:SS'))"
        ),
        "created_at": (
            "TEXT NOT NULL DEFAULT "
            "(to_char(now(), 'YYYY-MM-DD\"T\"HH24:MI:SS'))"
        ),
    }

    added = set()
    for col, definition in required_columns.items():
        if col not in existing:
            cur.execute(
                f"ALTER TABLE exercise_entries "
                f"ADD COLUMN IF NOT EXISTS {col} {definition}"
            )
            added.add(col)

    # Best-effort copy of data from common legacy column names.
    legacy_name_cols = [
        "exercise", "name", "activity", "activity_name", "exercise_type"
    ]
    if "exercise_name" in added:
        for legacy in legacy_name_cols:
            if legacy in existing:
                cur.execute(
                    f"UPDATE exercise_entries "
                    f"SET exercise_name = COALESCE({legacy}::TEXT, '') "
                    f"WHERE exercise_name = ''"
                )
                break
    if "calories_burned" in added:
        for legacy in ["calories", "total_calories", "kcal"]:
            if legacy in existing:
                cur.execute(
                    f"UPDATE exercise_entries "
                    f"SET calories_burned = COALESCE({legacy}::DOUBLE PRECISION, 0)"
                )
                break
    if "duration_minutes" in added:
        for legacy in ["duration", "minutes"]:
            if legacy in existing:
                cur.execute(
                    f"UPDATE exercise_entries "
                    f"SET duration_minutes = COALESCE({legacy}::DOUBLE PRECISION, 0)"
                )
                break

    # Legacy columns the app no longer writes must not block inserts.
    known = set(required_columns) | {"id", "user_id"}
    for col, info in existing.items():
        if col not in known and info["is_nullable"] == "NO":
            cur.execute(
                f'ALTER TABLE exercise_entries '
                f'ALTER COLUMN "{col}" DROP NOT NULL'
            )

    # The app stores entry_date as ISO text (YYYY-MM-DDTHH:MM:SS).
    if "entry_date" in existing and existing["entry_date"]["data_type"] in (
        "date", "timestamp without time zone", "timestamp with time zone"
    ):
        cur.execute(
            "ALTER TABLE exercise_entries ALTER COLUMN entry_date DROP DEFAULT"
        )
        cur.execute("""
            ALTER TABLE exercise_entries
            ALTER COLUMN entry_date TYPE TEXT
            USING to_char(entry_date, 'YYYY-MM-DD"T"HH24:MI:SS')
        """)


def migrate_food_macros(cur):
    """Copy protein/fat/carbs from legacy food_entries columns (if any) into
    the new macro columns. Only rows whose new macros are all zero are
    touched, so it is safe to run on every start."""
    cur.execute("""
        SELECT column_name FROM information_schema.columns
        WHERE table_schema = current_schema() AND table_name = 'food_entries'
    """)
    existing = {r["column_name"] for r in cur.fetchall()}

    def safe_num(col):
        # Tolerates legacy columns stored as TEXT or containing junk.
        return (
            "(CASE WHEN \"" + col + "\"::TEXT ~ '^[0-9]+(\\.[0-9]+)?$' "
            "THEN \"" + col + "\"::TEXT::DOUBLE PRECISION ELSE 0 END)"
        )

    targets = (
        ("protein", "protein_per_100g", "protein_g"),
        ("fat", "fat_per_100g", "fat_g"),
        ("carbs", "carbs_per_100g", "carbs_g"),
    )
    for macro, per100_col, total_col in targets:
        legacy = next(
            (c for c in LEGACY_MACRO_NAMES[macro] if c in existing), None
        )
        if not legacy:
            continue
        value = safe_num(legacy)
        if LEGACY_MACROS_ARE_PER_100G or "100" in legacy:
            cur.execute(f"""
                UPDATE food_entries
                SET {per100_col} = {value},
                    {total_col} = {value} * quantity_g / 100
                WHERE {per100_col} = 0 AND {total_col} = 0
            """)
        else:
            cur.execute(f"""
                UPDATE food_entries
                SET {total_col} = {value},
                    {per100_col} = CASE WHEN quantity_g > 0
                                        THEN {value} * 100 / quantity_g
                                        ELSE 0 END
                WHERE {per100_col} = 0 AND {total_col} = 0
            """)


def backfill_macros_from_history(user_id):
    """For entries that still have no macros, reuse the macros of the most
    recent entry with the same food name (case-insensitive) that has them.
    Returns the number of rows updated."""
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                UPDATE food_entries t
                SET protein_per_100g = s.p,
                    fat_per_100g = s.f,
                    carbs_per_100g = s.c,
                    protein_g = s.p * t.quantity_g / 100,
                    fat_g = s.f * t.quantity_g / 100,
                    carbs_g = s.c * t.quantity_g / 100
                FROM (
                    SELECT DISTINCT ON (user_id, LOWER(food_name))
                           user_id, LOWER(food_name) AS fname,
                           protein_per_100g AS p, fat_per_100g AS f,
                           carbs_per_100g AS c
                    FROM food_entries
                    WHERE user_id = %s
                      AND (protein_per_100g > 0 OR fat_per_100g > 0
                           OR carbs_per_100g > 0)
                    ORDER BY user_id, LOWER(food_name), id DESC
                ) s
                WHERE t.user_id = s.user_id
                  AND LOWER(t.food_name) = s.fname
                  AND t.protein_per_100g = 0
                  AND t.fat_per_100g = 0
                  AND t.carbs_per_100g = 0
            """, (user_id,))
            return cur.rowcount


def init_db():
    """Create compatible food/user tables plus the new exercise table."""
    with get_connection() as conn:
        with conn.cursor() as cur:
            # Same schema as the existing app.py.
            cur.execute("""
                CREATE TABLE IF NOT EXISTS users (
                    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
                    username TEXT NOT NULL UNIQUE,
                    password_hash TEXT NOT NULL,
                    password_salt TEXT NOT NULL,
                    created_at TEXT NOT NULL
                )
            """)
            cur.execute("""
                CREATE UNIQUE INDEX IF NOT EXISTS idx_users_username_lower
                ON users (LOWER(username))
            """)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS user_settings (
                    user_id BIGINT PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
                    daily_target DOUBLE PRECISION NOT NULL DEFAULT 2000
                )
            """)
            cur.execute("""
                ALTER TABLE user_settings
                ADD COLUMN IF NOT EXISTS maintenance_calories DOUBLE PRECISION NOT NULL DEFAULT 2000
            """)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS food_entries (
                    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
                    user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                    food_name TEXT NOT NULL,
                    calories_per_100g DOUBLE PRECISION NOT NULL,
                    quantity_g DOUBLE PRECISION NOT NULL,
                    calories DOUBLE PRECISION NOT NULL,
                    quantity_type TEXT NOT NULL DEFAULT 'Grams (g)',
                    unit_count DOUBLE PRECISION NOT NULL DEFAULT 0,
                    unit_weight DOUBLE PRECISION NOT NULL DEFAULT 0,
                    entry_date TEXT NOT NULL,
                    source TEXT NOT NULL DEFAULT 'Manual',
                    created_at TEXT NOT NULL
                )
            """)
            # Macronutrient columns. Added with ALTER so existing food
            # rows are kept (they get 0 until imported or edited).
            for macro_col in (
                "protein_per_100g", "fat_per_100g", "carbs_per_100g",
                "protein_g", "fat_g", "carbs_g"
            ):
                cur.execute(f"""
                    ALTER TABLE food_entries
                    ADD COLUMN IF NOT EXISTS {macro_col}
                    DOUBLE PRECISION NOT NULL DEFAULT 0
                """)
            # Import macros from older columns (protein, fat, carbs, ...).
            migrate_food_macros(cur)
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_food_user_date
                ON food_entries(user_id, entry_date)
            """)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS app_meta (
                    key TEXT PRIMARY KEY,
                    value TEXT
                )
            """)

            # New table. All records are scoped to the logged-in user.
            cur.execute("""
                CREATE TABLE IF NOT EXISTS exercise_entries (
                    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
                    user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                    exercise_name TEXT NOT NULL,
                    category TEXT NOT NULL,
                    duration_minutes DOUBLE PRECISION NOT NULL DEFAULT 0,
                    body_weight_kg DOUBLE PRECISION NOT NULL DEFAULT 0,
                    lifted_weight_kg DOUBLE PRECISION NOT NULL DEFAULT 0,
                    sets INTEGER NOT NULL DEFAULT 0,
                    reps INTEGER NOT NULL DEFAULT 0,
                    calories_burned DOUBLE PRECISION NOT NULL,
                    source TEXT NOT NULL DEFAULT 'API Ninjas',
                    entry_date TEXT NOT NULL,
                    created_at TEXT NOT NULL
                )
            """)
            # Upgrade an older, differently-structured exercise_entries table
            # so that all columns used by this app exist.
            migrate_exercise_table(cur)
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_exercise_user_date
                ON exercise_entries(user_id, entry_date)
            """)

            # Independent body-weight history.
            cur.execute("""
                CREATE TABLE IF NOT EXISTS weight_entries (
                    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
                    user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                    weight_kg DOUBLE PRECISION NOT NULL CHECK (weight_kg > 0),
                    entry_date DATE NOT NULL,
                    notes TEXT NOT NULL DEFAULT '',
                    created_at TEXT NOT NULL
                )
            """)
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_weight_user_date
                ON weight_entries(user_id, entry_date)
            """)

            # One consolidated, user-specific record per calendar date.
            cur.execute("""
                CREATE TABLE IF NOT EXISTS daily_summary (
                    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
                    user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                    entry_date DATE NOT NULL,
                    maintenance_calories DOUBLE PRECISION NOT NULL DEFAULT 2000,
                    calories_consumed DOUBLE PRECISION NOT NULL DEFAULT 0,
                    calories_burned DOUBLE PRECISION NOT NULL DEFAULT 0,
                    current_weight DOUBLE PRECISION,
                    calorie_balance DOUBLE PRECISION NOT NULL DEFAULT 0,
                    created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                    updated_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                    UNIQUE(user_id, entry_date)
                )
            """)
            # Daily macro totals.
            for macro_col in (
                "protein_consumed", "fat_consumed", "carbs_consumed"
            ):
                cur.execute(f"""
                    ALTER TABLE daily_summary
                    ADD COLUMN IF NOT EXISTS {macro_col}
                    DOUBLE PRECISION NOT NULL DEFAULT 0
                """)
            cur.execute("""
                CREATE INDEX IF NOT EXISTS idx_daily_summary_user_date
                ON daily_summary(user_id, entry_date DESC)
            """)


# ============================================================
# AUTHENTICATION - compatible with app.py accounts
# ============================================================
def hash_password(password, salt=None):
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), salt, 310_000
    )
    return digest.hex(), salt.hex()


def verify_password(password, stored_hash, stored_salt):
    try:
        salt = bytes.fromhex(stored_salt)
        candidate, _ = hash_password(password, salt)
        return hmac.compare_digest(candidate, stored_hash)
    except (ValueError, TypeError):
        return False


def create_user(username, password):
    username = username.strip()
    if len(username) < 3:
        return False, "Username must contain at least 3 characters."
    if len(password) < 8:
        return False, "Password must contain at least 8 characters."

    password_hash, salt = hash_password(password)
    now = datetime.now().isoformat(timespec="seconds")

    try:
        with get_connection() as conn:
            with conn.cursor() as cur:
                cur.execute("""
                    INSERT INTO users
                    (username, password_hash, password_salt, created_at)
                    VALUES (%s, %s, %s, %s)
                    RETURNING id
                """, (username, password_hash, salt, now))
                user_id = cur.fetchone()["id"]
                cur.execute("""
                    INSERT INTO user_settings(user_id, daily_target)
                    VALUES (%s, %s)
                """, (user_id, 2000))
        return True, "Account created. You are now logged in."
    except errors.UniqueViolation:
        return False, "That username already exists. Please choose another."


def authenticate_user(username, password):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM users WHERE LOWER(username)=LOWER(%s)",
                (username.strip(),)
            )
            user = cur.fetchone()

    if user and verify_password(
        password, user["password_hash"], user["password_salt"]
    ):
        return {"id": user["id"], "username": user["username"]}
    return None


# ============================================================
# USER TARGET
# ============================================================
def get_target(user_id):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT daily_target FROM user_settings WHERE user_id=%s",
                (user_id,)
            )
            row = cur.fetchone()
    return float(row["daily_target"]) if row else 2000.0


def update_target(user_id, target):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO user_settings(user_id, daily_target)
                VALUES (%s, %s)
                ON CONFLICT(user_id) DO UPDATE
                SET daily_target=EXCLUDED.daily_target
            """, (user_id, float(target)))


def get_maintenance_calories(user_id):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT maintenance_calories FROM user_settings WHERE user_id=%s",
                (user_id,)
            )
            row = cur.fetchone()
    return float(row["maintenance_calories"]) if row else 2000.0


def update_maintenance_calories(user_id, calories):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO user_settings(user_id, daily_target, maintenance_calories)
                VALUES (%s, %s, %s)
                ON CONFLICT(user_id) DO UPDATE
                SET maintenance_calories=EXCLUDED.maintenance_calories
            """, (user_id, get_target(user_id), float(calories)))


# ============================================================
# FOOD DATABASE FUNCTIONS - same food_entries schema as app.py
# (plus protein / fat / carbs)
# ============================================================
def add_food(user_id, food_name, calories_per_100g, quantity_g,
             quantity_type="Grams (g)", unit_count=0, unit_weight=0,
             source="Manual", protein_per_100g=0.0, fat_per_100g=0.0,
             carbs_per_100g=0.0):
    quantity_g = float(quantity_g)
    calories_per_100g = float(calories_per_100g)
    protein_per_100g = float(protein_per_100g or 0)
    fat_per_100g = float(fat_per_100g or 0)
    carbs_per_100g = float(carbs_per_100g or 0)

    if not food_name.strip():
        raise ValueError("Food name is required.")
    if quantity_g <= 0 or calories_per_100g < 0:
        raise ValueError("Quantity must be above zero and calories cannot be negative.")
    if protein_per_100g < 0 or fat_per_100g < 0 or carbs_per_100g < 0:
        raise ValueError("Protein, fat and carbs cannot be negative.")

    calories = calories_per_100g * quantity_g / 100
    protein_g = protein_per_100g * quantity_g / 100
    fat_g = fat_per_100g * quantity_g / 100
    carbs_g = carbs_per_100g * quantity_g / 100
    now = datetime.now().isoformat(timespec="seconds")

    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO food_entries
                (user_id, food_name, calories_per_100g, quantity_g, calories,
                 quantity_type, unit_count, unit_weight, entry_date, source, created_at,
                 protein_per_100g, fat_per_100g, carbs_per_100g,
                 protein_g, fat_g, carbs_g)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s,
                        %s, %s, %s, %s, %s, %s)
            """, (
                user_id, food_name.strip(), calories_per_100g, quantity_g,
                calories, quantity_type, float(unit_count), float(unit_weight),
                now, source, now,
                protein_per_100g, fat_per_100g, carbs_per_100g,
                protein_g, fat_g, carbs_g
            ))


def add_food_actual(user_id, food_name, actual_calories,
                    protein_g=0.0, fat_g=0.0, carbs_g=0.0):
    """Add a manual food entry using ACTUAL (total) calories and optional
    actual macro grams. No quantity is needed.

    Stored in the same food_entries table: the entry is saved as a nominal
    100 g portion, so calories_per_100g == calories == the actual calories
    (and likewise for macros). All existing summaries, history, copy and
    backfill logic therefore work unchanged."""
    actual_calories = float(actual_calories)
    protein_g = float(protein_g or 0)
    fat_g = float(fat_g or 0)
    carbs_g = float(carbs_g or 0)
    if actual_calories < 0:
        raise ValueError("Calories cannot be negative.")
    add_food(
        user_id=user_id,
        food_name=food_name,
        calories_per_100g=actual_calories,
        quantity_g=100.0,
        quantity_type=ACTUAL_CAL_TYPE,
        unit_count=0,
        unit_weight=0,
        source="Manual",
        protein_per_100g=protein_g,
        fat_per_100g=fat_g,
        carbs_per_100g=carbs_g,
    )


def get_food_entries(user_id, selected_day=None):
    selected_day = selected_day or date.today()
    start = datetime.combine(
        selected_day, datetime.min.time()
    ).isoformat()
    end = (
        datetime.combine(selected_day, datetime.min.time())
        + timedelta(days=1)
    ).isoformat()

    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                SELECT * FROM food_entries
                WHERE user_id=%s AND entry_date >= %s AND entry_date < %s
                ORDER BY id DESC
            """, (user_id, start, end))
            rows = cur.fetchall()
    return [dict(row) for row in rows]


def update_food(user_id, food_id, quantity_g, quantity_type,
                unit_count, unit_weight, protein_per_100g=None,
                fat_per_100g=None, carbs_per_100g=None):
    """Update quantity (and optionally the per-100 g macros) of an entry.
    Calories and macro totals are recalculated from the per-100 g values."""
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                SELECT calories_per_100g, protein_per_100g,
                       fat_per_100g, carbs_per_100g
                FROM food_entries WHERE id=%s AND user_id=%s
            """, (food_id, user_id))
            row = cur.fetchone()
            if not row:
                return False

            p100 = float(
                row["protein_per_100g"] if protein_per_100g is None
                else protein_per_100g
            )
            f100 = float(
                row["fat_per_100g"] if fat_per_100g is None
                else fat_per_100g
            )
            c100 = float(
                row["carbs_per_100g"] if carbs_per_100g is None
                else carbs_per_100g
            )

            calories = (
                float(row["calories_per_100g"]) * float(quantity_g) / 100
            )
            cur.execute("""
                UPDATE food_entries
                SET quantity_g=%s, calories=%s, quantity_type=%s,
                    unit_count=%s, unit_weight=%s,
                    protein_per_100g=%s, fat_per_100g=%s, carbs_per_100g=%s,
                    protein_g=%s, fat_g=%s, carbs_g=%s
                WHERE id=%s AND user_id=%s
            """, (
                float(quantity_g), calories, quantity_type,
                float(unit_count), float(unit_weight),
                p100, f100, c100,
                p100 * float(quantity_g) / 100,
                f100 * float(quantity_g) / 100,
                c100 * float(quantity_g) / 100,
                food_id, user_id
            ))
    return True


def update_food_actual(user_id, food_id, actual_calories,
                       protein_g, fat_g, carbs_g):
    """Edit an 'Actual calories' entry: the values are totals, not per 100 g."""
    actual_calories = float(actual_calories)
    protein_g = float(protein_g or 0)
    fat_g = float(fat_g or 0)
    carbs_g = float(carbs_g or 0)
    if actual_calories < 0 or protein_g < 0 or fat_g < 0 or carbs_g < 0:
        raise ValueError("Calories and macros cannot be negative.")
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                UPDATE food_entries
                SET quantity_g=100, quantity_type=%s,
                    unit_count=0, unit_weight=0,
                    calories_per_100g=%s, calories=%s,
                    protein_per_100g=%s, fat_per_100g=%s, carbs_per_100g=%s,
                    protein_g=%s, fat_g=%s, carbs_g=%s
                WHERE id=%s AND user_id=%s
            """, (
                ACTUAL_CAL_TYPE,
                actual_calories, actual_calories,
                protein_g, fat_g, carbs_g,
                protein_g, fat_g, carbs_g,
                food_id, user_id
            ))
            return cur.rowcount > 0


def delete_food(user_id, food_id):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "DELETE FROM food_entries WHERE id=%s AND user_id=%s",
                (food_id, user_id)
            )


# ============================================================
# EXERCISE DATABASE FUNCTIONS
# ============================================================
def add_exercise(
    user_id, exercise_name, category, duration_minutes,
    body_weight_kg, lifted_weight_kg, sets, reps,
    calories_burned, source
):
    if not exercise_name.strip():
        raise ValueError("Exercise name is required.")
    if float(calories_burned) < 0:
        raise ValueError("Calories burned cannot be negative.")
    if float(duration_minutes) < 0:
        raise ValueError("Duration cannot be negative.")

    now = datetime.now().isoformat(timespec="seconds")

    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO exercise_entries
                (user_id, exercise_name, category, duration_minutes,
                 body_weight_kg, lifted_weight_kg, sets, reps,
                 calories_burned, source, entry_date, created_at)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            """, (
                user_id, exercise_name.strip(), category,
                float(duration_minutes), float(body_weight_kg),
                float(lifted_weight_kg), int(sets), int(reps),
                float(calories_burned), source, now, now
            ))


def get_exercise_entries(user_id, selected_day=None):
    selected_day = selected_day or date.today()
    start = datetime.combine(
        selected_day, datetime.min.time()
    ).isoformat()
    end = (
        datetime.combine(selected_day, datetime.min.time())
        + timedelta(days=1)
    ).isoformat()

    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                SELECT * FROM exercise_entries
                WHERE user_id=%s AND entry_date >= %s AND entry_date < %s
                ORDER BY id DESC
            """, (user_id, start, end))
            rows = cur.fetchall()
    return [dict(row) for row in rows]


def delete_exercise(user_id, exercise_id):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                DELETE FROM exercise_entries
                WHERE id=%s AND user_id=%s
            """, (exercise_id, user_id))


def copy_food_entry(user_id, food_id, destination_day):
    destination_stamp = datetime.combine(destination_day, datetime.min.time()).isoformat()
    now = datetime.now().isoformat(timespec="seconds")
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO food_entries
                (user_id, food_name, calories_per_100g, quantity_g, calories,
                 quantity_type, unit_count, unit_weight, entry_date, source, created_at,
                 protein_per_100g, fat_per_100g, carbs_per_100g,
                 protein_g, fat_g, carbs_g)
                SELECT user_id, food_name, calories_per_100g, quantity_g, calories,
                       quantity_type, unit_count, unit_weight, %s, source, %s,
                       protein_per_100g, fat_per_100g, carbs_per_100g,
                       protein_g, fat_g, carbs_g
                FROM food_entries WHERE id=%s AND user_id=%s
            """, (destination_stamp, now, food_id, user_id))
            return cur.rowcount > 0


def copy_exercise_entry(user_id, exercise_id, destination_day):
    destination_stamp = datetime.combine(destination_day, datetime.min.time()).isoformat()
    now = datetime.now().isoformat(timespec="seconds")
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO exercise_entries
                (user_id, exercise_name, category, duration_minutes,
                 body_weight_kg, lifted_weight_kg, sets, reps,
                 calories_burned, source, entry_date, created_at)
                SELECT user_id, exercise_name, category, duration_minutes,
                       body_weight_kg, lifted_weight_kg, sets, reps,
                       calories_burned, source, %s, %s
                FROM exercise_entries WHERE id=%s AND user_id=%s
            """, (destination_stamp, now, exercise_id, user_id))
            return cur.rowcount > 0


def add_weight(user_id, weight_kg, entry_day, notes=""):
    weight_kg = float(weight_kg)
    if weight_kg <= 0:
        raise ValueError("Weight must be greater than zero.")
    now = datetime.now().isoformat(timespec="seconds")
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO weight_entries
                (user_id, weight_kg, entry_date, notes, created_at)
                VALUES (%s, %s, %s, %s, %s)
            """, (user_id, weight_kg, entry_day, notes.strip(), now))


def get_weights(user_id):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                SELECT * FROM weight_entries
                WHERE user_id=%s
                ORDER BY entry_date DESC, id DESC
            """, (user_id,))
            return [dict(row) for row in cur.fetchall()]


def update_weight(user_id, weight_id, weight_kg, entry_day, notes=""):
    weight_kg = float(weight_kg)
    if weight_kg <= 0:
        raise ValueError("Weight must be greater than zero.")
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                UPDATE weight_entries
                SET weight_kg=%s, entry_date=%s, notes=%s
                WHERE id=%s AND user_id=%s
            """, (weight_kg, entry_day, notes.strip(), weight_id, user_id))
            return cur.rowcount > 0


def delete_weight(user_id, weight_id):
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                DELETE FROM weight_entries WHERE id=%s AND user_id=%s
            """, (weight_id, user_id))


def copy_day_entries(user_id, source_day, destination_day):
    """Copy all food and exercise rows from one date to another, without deleting originals."""
    if source_day == destination_day:
        raise ValueError("Source and destination dates must be different.")
    source_start = datetime.combine(source_day, datetime.min.time()).isoformat()
    source_end = (datetime.combine(source_day, datetime.min.time()) + timedelta(days=1)).isoformat()
    destination_stamp = datetime.combine(destination_day, datetime.min.time()).isoformat()
    now = datetime.now().isoformat(timespec="seconds")
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                INSERT INTO food_entries
                (user_id, food_name, calories_per_100g, quantity_g, calories,
                 quantity_type, unit_count, unit_weight, entry_date, source, created_at,
                 protein_per_100g, fat_per_100g, carbs_per_100g,
                 protein_g, fat_g, carbs_g)
                SELECT user_id, food_name, calories_per_100g, quantity_g, calories,
                       quantity_type, unit_count, unit_weight, %s, source, %s,
                       protein_per_100g, fat_per_100g, carbs_per_100g,
                       protein_g, fat_g, carbs_g
                FROM food_entries
                WHERE user_id=%s AND entry_date >= %s AND entry_date < %s
            """, (destination_stamp, now, user_id, source_start, source_end))
            food_count = cur.rowcount
            cur.execute("""
                INSERT INTO exercise_entries
                (user_id, exercise_name, category, duration_minutes,
                 body_weight_kg, lifted_weight_kg, sets, reps,
                 calories_burned, source, entry_date, created_at)
                SELECT user_id, exercise_name, category, duration_minutes,
                       body_weight_kg, lifted_weight_kg, sets, reps,
                       calories_burned, source, %s, %s
                FROM exercise_entries
                WHERE user_id=%s AND entry_date >= %s AND entry_date < %s
            """, (destination_stamp, now, user_id, source_start, source_end))
            exercise_count = cur.rowcount
    return food_count, exercise_count


def sync_daily_summary(user_id):
    """Refresh one database summary row per date from food, exercise and weight logs.

    Historical maintenance values are retained. The current date takes the
    latest maintenance setting; consumed/burned/weight/macro values are
    refreshed from their source tables whenever the history is opened.
    """
    maintenance = get_maintenance_calories(user_id)
    today = date.today()
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                WITH food AS (
                    SELECT SUBSTRING(entry_date FROM 1 FOR 10)::DATE AS day,
                           COALESCE(SUM(calories), 0)::DOUBLE PRECISION AS consumed,
                           COALESCE(SUM(protein_g), 0)::DOUBLE PRECISION AS protein,
                           COALESCE(SUM(fat_g), 0)::DOUBLE PRECISION AS fat,
                           COALESCE(SUM(carbs_g), 0)::DOUBLE PRECISION AS carbs
                    FROM food_entries
                    WHERE user_id=%s
                    GROUP BY SUBSTRING(entry_date FROM 1 FOR 10)::DATE
                ),
                exercise AS (
                    SELECT SUBSTRING(entry_date FROM 1 FOR 10)::DATE AS day,
                           COALESCE(SUM(calories_burned), 0)::DOUBLE PRECISION AS burned
                    FROM exercise_entries
                    WHERE user_id=%s
                    GROUP BY SUBSTRING(entry_date FROM 1 FOR 10)::DATE
                ),
                weights AS (
                    SELECT DISTINCT ON (entry_date) entry_date AS day, weight_kg
                    FROM weight_entries
                    WHERE user_id=%s
                    ORDER BY entry_date, id DESC
                ),
                all_days AS (
                    SELECT day FROM food
                    UNION SELECT day FROM exercise
                    UNION SELECT day FROM weights
                    UNION SELECT entry_date FROM daily_summary WHERE user_id=%s
                    UNION SELECT %s::DATE
                )
                INSERT INTO daily_summary (
                    user_id, entry_date, maintenance_calories,
                    calories_consumed, calories_burned, current_weight,
                    calorie_balance, protein_consumed, fat_consumed,
                    carbs_consumed, updated_at
                )
                SELECT %s, d.day, %s,
                       COALESCE(f.consumed, 0),
                       COALESCE(e.burned, 0),
                       w.weight_kg,
                       COALESCE(f.consumed, 0) - (%s + COALESCE(e.burned, 0)),
                       COALESCE(f.protein, 0),
                       COALESCE(f.fat, 0),
                       COALESCE(f.carbs, 0),
                       CURRENT_TIMESTAMP
                FROM all_days d
                LEFT JOIN food f ON f.day=d.day
                LEFT JOIN exercise e ON e.day=d.day
                LEFT JOIN weights w ON w.day=d.day
                ON CONFLICT (user_id, entry_date) DO UPDATE SET
                    maintenance_calories = CASE
                        WHEN daily_summary.entry_date=%s
                        THEN EXCLUDED.maintenance_calories
                        ELSE daily_summary.maintenance_calories
                    END,
                    calories_consumed=EXCLUDED.calories_consumed,
                    calories_burned=EXCLUDED.calories_burned,
                    current_weight=EXCLUDED.current_weight,
                    calorie_balance=EXCLUDED.calories_consumed - (
                        CASE WHEN daily_summary.entry_date=%s
                             THEN EXCLUDED.maintenance_calories
                             ELSE daily_summary.maintenance_calories END
                        + EXCLUDED.calories_burned
                    ),
                    protein_consumed=EXCLUDED.protein_consumed,
                    fat_consumed=EXCLUDED.fat_consumed,
                    carbs_consumed=EXCLUDED.carbs_consumed,
                    updated_at=CURRENT_TIMESTAMP
            """, (
                user_id, user_id, user_id, user_id, today,
                user_id, maintenance, maintenance, today, today
            ))


def get_history(user_id, days=10):
    """Return the most recent day-wise records stored in daily_summary."""
    sync_daily_summary(user_id)
    with get_connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""
                SELECT entry_date AS "Date",
                       maintenance_calories AS "Maintenance calories",
                       calories_consumed AS "Calories consumed",
                       calories_burned AS "Calories burned",
                       current_weight AS "Current weight (kg)",
                       calorie_balance AS "Deficit / surplus",
                       protein_consumed AS "Protein (g)",
                       fat_consumed AS "Fat (g)",
                       carbs_consumed AS "Carbs (g)"
                FROM daily_summary
                WHERE user_id=%s
                ORDER BY entry_date DESC
                LIMIT %s
            """, (user_id, days))
            rows = cur.fetchall()
    return [dict(row) for row in rows]


# ============================================================
# USDA FOODDATA CENTRAL
# ============================================================
def get_calories_from_nutrients(nutrients):
    kcal = None
    kj = None

    for nutrient in nutrients:
        nutrient_info = nutrient.get("nutrient", {})
        nutrient_id = (
            nutrient.get("nutrientId")
            or nutrient.get("nutrientNumber")
            or nutrient_info.get("id")
        )
        name = (
            nutrient.get("nutrientName")
            or nutrient_info.get("name")
            or ""
        ).lower()
        unit = (
            nutrient.get("unitName")
            or nutrient_info.get("unitName")
            or ""
        ).lower()
        value = nutrient.get("value")
        if value is None:
            value = nutrient.get("amount")

        try:
            value = float(value)
        except (TypeError, ValueError):
            continue

        if value < 0:
            continue

        if unit == "kcal" and (
            nutrient_id in (1008, 2047, 2048) or "energy" in name
        ):
            if nutrient_id == 1008:
                return value
            if kcal is None:
                kcal = value
        elif unit == "kj" and (
            nutrient_id == 1062 or "energy" in name
        ):
            kj = value

    if kcal is not None:
        return kcal
    if kj is not None:
        return kj / 4.184
    return None


def get_macros_from_nutrients(nutrients):
    """Extract protein, total fat and carbohydrate (g per 100 g) from a
    USDA foodNutrients list. Missing values are returned as 0.0.

    USDA nutrient ids: protein 1003, total fat 1004, carbohydrate 1005.
    """
    macros = {"protein": None, "fat": None, "carbs": None}
    id_map = {1003: "protein", 1004: "fat", 1005: "carbs"}

    for nutrient in nutrients:
        nutrient_info = nutrient.get("nutrient", {})
        nutrient_id = (
            nutrient.get("nutrientId")
            or nutrient.get("nutrientNumber")
            or nutrient_info.get("id")
        )
        name = (
            nutrient.get("nutrientName")
            or nutrient_info.get("name")
            or ""
        ).lower()
        unit = (
            nutrient.get("unitName")
            or nutrient_info.get("unitName")
            or ""
        ).lower()
        value = nutrient.get("value")
        if value is None:
            value = nutrient.get("amount")

        try:
            value = float(value)
        except (TypeError, ValueError):
            continue
        if value < 0 or (unit and unit != "g"):
            continue

        try:
            nutrient_id = int(nutrient_id) if nutrient_id is not None else None
        except (TypeError, ValueError):
            nutrient_id = None

        key = id_map.get(nutrient_id)
        if key is None:
            if name == "protein":
                key = "protein"
            elif name.startswith("total lipid") or name == "fat":
                key = "fat"
            elif name.startswith("carbohydrate, by difference"):
                key = "carbs"
        if key and macros[key] is None:
            macros[key] = value

    return {k: (v if v is not None else 0.0) for k, v in macros.items()}


@st.cache_data(ttl=60, show_spinner=False)
def search_food_api(food_name, api_key):
    params = {
        "query": food_name,
        "pageSize": 20,
        "pageNumber": 1,
        "api_key": api_key
    }

    for attempt in range(3):
        try:
            response = requests.get(
                USDA_API_URL, params=params, timeout=20
            )
            if response.status_code == 429:
                if attempt < 2:
                    time.sleep(2 ** attempt)
                    continue
                return [], "USDA rate limit exceeded. Try again shortly."

            response.raise_for_status()
            data = response.json()
            results = []

            for product in data.get("foods", []):
                calories = get_calories_from_nutrients(
                    product.get("foodNutrients", [])
                )
                if calories is None or calories < 0:
                    continue

                macros = get_macros_from_nutrients(
                    product.get("foodNutrients", [])
                )

                name = (product.get("description") or "").strip()
                if not name:
                    continue

                serving_weight = None
                serving_size = ""
                serving = product.get("servingSize")
                serving_unit = product.get("servingSizeUnit", "")

                if serving is not None:
                    try:
                        serving = float(serving)
                        serving_size = f"{serving:g} {serving_unit}"
                        if serving_unit.lower() == "g" and serving > 0:
                            serving_weight = serving
                    except (TypeError, ValueError):
                        pass

                if serving_weight is None:
                    portions = product.get("foodPortions", [])
                    if portions:
                        try:
                            weight = float(
                                portions[0].get("gramWeight")
                            )
                            if weight > 0:
                                serving_weight = weight
                                serving_size = (
                                    portions[0].get("modifier") or ""
                                )
                        except (TypeError, ValueError):
                            pass

                results.append({
                    "name": name,
                    "calories": float(calories),
                    "protein": float(macros["protein"]),
                    "fat": float(macros["fat"]),
                    "carbs": float(macros["carbs"]),
                    "brand": (
                        product.get("brandOwner")
                        or product.get("brandName")
                        or ""
                    ),
                    "serving_weight": serving_weight,
                    "serving_size": serving_size
                })

            return results, None

        except requests.exceptions.HTTPError as exc:
            status = (
                exc.response.status_code
                if exc.response is not None else None
            )
            if status in (401, 403):
                return [], "Invalid USDA API key. Check your key."
            return [], f"USDA API error: {exc}"

        except requests.exceptions.RequestException as exc:
            if attempt < 2:
                time.sleep(2 ** attempt)
            else:
                return [], f"Connection error: {exc}"

        except ValueError:
            return [], "USDA returned an invalid response."

    return [], "Unable to retrieve food information."


# ============================================================
# API NINJAS EXERCISE SEARCH + CALORIE ESTIMATE
# ============================================================
@st.cache_data(ttl=300, show_spinner=False)
def search_ninjas_exercises(search_term, exercise_type, api_key):
    """Search exercise names/details. API Ninjas returns up to 5 matches."""
    params = {"name": search_term, "type": exercise_type}
    headers = {"X-Api-Key": api_key}

    response = requests.get(
        NINJAS_EXERCISES_URL,
        params=params,
        headers=headers,
        timeout=20
    )
    response.raise_for_status()
    data = response.json()

    if not isinstance(data, list):
        raise ValueError("Unexpected response from API Ninjas.")
    return data


def estimate_ninjas_calories(
    activity, body_weight_kg, duration_minutes, api_key
):
    """
    API Ninjas expects body weight in pounds and duration in minutes.
    Its calorie estimate does NOT use lifted weight, sets or reps.
    Those are captured separately in the exercise diary.
    """
    weight_lb = float(body_weight_kg) * 2.2046226218

    params = {
        "activity": activity,
        "weight": round(weight_lb),
        "duration": int(duration_minutes)
    }
    headers = {"X-Api-Key": api_key}

    response = requests.get(
        NINJAS_CALORIES_URL,
        params=params,
        headers=headers,
        timeout=20
    )
    response.raise_for_status()
    data = response.json()

    if not isinstance(data, list) or not data:
        raise ValueError(
            "API Ninjas returned no calorie estimate for this activity."
        )

    # The first match is the API's best match.
    result = data[0]
    calories = result.get("total_calories")

    if calories is None:
        raise ValueError("The API response did not include total_calories.")

    return {
        "matched_name": result.get("name", activity),
        "calories": float(calories),
        "calories_per_hour": float(
            result.get("calories_per_hour", 0)
        )
    }


# ============================================================
# INITIALIZE DATABASE
# ============================================================
try:
    init_db()
except KeyError as exc:
    st.error(
        f"Missing Supabase secret: {exc}. "
        "Add the [postgres] settings in Streamlit Secrets."
    )
    st.stop()
except psycopg2.Error as exc:
    st.error(f"Could not connect to Supabase PostgreSQL: {exc}")
    st.stop()


# ============================================================
# SESSION STATE
# ============================================================
if "user" not in st.session_state:
    st.session_state.user = None
if "selected_food" not in st.session_state:
    st.session_state.selected_food = None


# ============================================================
# LOGIN / REGISTRATION
# ============================================================
if st.session_state.user is None:
    st.title("🥗 My Calorie & Exercise Tracker")
    st.caption(
        "Track food intake, workouts, calories burned and daily net calories."
    )

    login_tab, register_tab = st.tabs(["Login", "Create account"])

    with login_tab:
        with st.form("login_form"):
            login_username = st.text_input("Username")
            login_password = st.text_input(
                "Password", type="password"
            )
            login_submit = st.form_submit_button(
                "Login", use_container_width=True
            )

        if login_submit:
            user = authenticate_user(
                login_username, login_password
            )
            if user:
                st.session_state.user = user
                st.session_state.selected_food = None
                st.rerun()
            else:
                st.error("Incorrect username or password.")

    with register_tab:
        with st.form("register_form"):
            new_username = st.text_input("Choose a username")
            new_password = st.text_input(
                "Choose a password", type="password"
            )
            confirm_password = st.text_input(
                "Confirm password", type="password"
            )
            register_submit = st.form_submit_button(
                "Create account", use_container_width=True
            )

        if register_submit:
            if new_password != confirm_password:
                st.error("Passwords do not match.")
            else:
                ok, message = create_user(
                    new_username, new_password
                )
                if ok:
                    user = authenticate_user(
                        new_username, new_password
                    )
                    st.session_state.user = user
                    st.success(message)
                    st.rerun()
                else:
                    st.error(message)

    st.stop()


# ============================================================
# MAIN APP / SIDEBAR
# ============================================================
user = st.session_state.user
user_id = user["id"]

with st.sidebar:
    st.title("⚙️ Account")
    st.write(f"Logged in as **{user['username']}**")

    if st.button("Log out", use_container_width=True):
        st.session_state.user = None
        st.session_state.selected_food = None
        st.rerun()

    st.divider()
    st.subheader("API configuration")

    usda_api_key = st.text_input(
        "USDA API Key",
        type="password",
        placeholder="Enter USDA API key",
        help="Used for food searches in this session."
    )
    st.caption("USDA key: https://api.data.gov/signup/")

    ninjas_api_key = st.text_input(
        "API Ninjas Key",
        type="password",
        placeholder="Enter API Ninjas key",
        help="Used for exercise search and calorie estimates."
    )
    st.caption("API Ninjas: https://api-ninjas.com/")

    st.divider()
    if st.button("Fill missing macros from my past entries",
                 use_container_width=True):
        filled = backfill_macros_from_history(user_id)
        st.success(f"Updated {filled} food entries.")

    st.divider()
    st.caption(
        "API keys entered here are held in the Streamlit session "
        "and are not written to the food or exercise tables."
    )


st.title("🥗 My Calorie & Exercise Tracker")
st.caption(f"Logged in as: {user['username']}")

# ============================================================
# DAILY TARGET
# ============================================================
st.subheader("🎯 Daily Net Calorie Target")

target = get_target(user_id)
new_target = st.number_input(
    "Set your daily net calorie target (kcal)",
    min_value=100,
    max_value=10000,
    value=int(target),
    step=50,
    key=f"target_{user_id}"
)

if float(new_target) != float(target):
    update_target(user_id, new_target)
    st.success("Your daily net calorie target has been updated.")

maintenance_calories = get_maintenance_calories(user_id)
new_maintenance_calories = st.number_input(
    "Set your maintenance calories (kcal/day, excluding exercise)",
    min_value=500, max_value=10000,
    value=int(maintenance_calories), step=50,
    key=f"maintenance_{user_id}"
)
if float(new_maintenance_calories) != float(maintenance_calories):
    update_maintenance_calories(user_id, new_maintenance_calories)
    st.success("Your maintenance calories have been updated.")

st.caption(
    "Maintenance calories are your baseline daily energy use, excluding exercise. "
    "Daily deficit/surplus = maintenance calories + exercise calories burned − food calories. "
    "The net calorie target remains available as your existing target."
)

# ============================================================
# DAILY DASHBOARD
# ============================================================
dashboard_day = st.date_input(
    "Dashboard date", value=date.today(), key="dashboard_day"
)

dashboard_food = get_food_entries(user_id, dashboard_day)
dashboard_exercise = get_exercise_entries(user_id, dashboard_day)

consumed_today = sum(
    float(row["calories"]) for row in dashboard_food
)
burned_today = sum(
    float(row["calories_burned"]) for row in dashboard_exercise
)
protein_today = sum(
    float(row.get("protein_g") or 0) for row in dashboard_food
)
fat_today = sum(
    float(row.get("fat_g") or 0) for row in dashboard_food
)
carbs_today = sum(
    float(row.get("carbs_g") or 0) for row in dashboard_food
)
# Net calories after accounting for baseline maintenance and exercise.
# Negative = calorie deficit; positive = calorie surplus.
net_calories = consumed_today - (float(new_maintenance_calories) + burned_today)
calorie_deficit = -net_calories

# Keep the existing daily net-intake target calculation unchanged.
net_intake = consumed_today - burned_today
net_vs_target = net_intake - float(new_target)
remaining = float(new_target) - net_intake

st.divider()
st.subheader(f"📊 Daily Dashboard — {dashboard_day.strftime('%d %b %Y')}")

m1, m2, m3, m4, m5 = st.columns(5)
m1.metric("Calories consumed", f"{consumed_today:,.0f} kcal")
m2.metric("Exercise calories burned", f"{burned_today:,.0f} kcal")
m3.metric("Maintenance calories", f"{float(new_maintenance_calories):,.0f} kcal")
m4.metric("Net calories", f"{net_calories:,.0f} kcal")
m5.metric(
    "Daily deficit / surplus",
    f"{calorie_deficit:+,.0f} kcal",
    delta=("Deficit" if calorie_deficit >= 0 else "Surplus"),
    delta_color="normal" if calorie_deficit >= 0 else "inverse"
)

# Macronutrients eaten on the selected date.
mac1, mac2, mac3 = st.columns(3)
mac1.metric("Protein", f"{protein_today:,.1f} g")
mac2.metric("Fat", f"{fat_today:,.1f} g")
mac3.metric("Carbohydrates", f"{carbs_today:,.1f} g")

# Progress bar tracks the existing net-intake target (food minus exercise),
# not the maintenance-based deficit/surplus figure shown above.
progress = max(
    0.0,
    min(net_intake / max(float(new_target), 1), 1.0)
)
st.progress(progress)

if remaining > 0:
    st.success(
        f"Net intake is {remaining:,.0f} kcal below your daily net target."
    )
elif remaining < 0:
    st.warning(
        f"Net intake is {abs(remaining):,.0f} kcal above your daily net target."
    )
else:
    st.info("You are exactly at your daily net calorie target.")

st.divider()


# ============================================================
# MAIN SECTIONS AS SELECTABLE TABS
# ============================================================
tab_food, tab_exercise, tab_weight, tab_copy, tab_history = st.tabs([
    "🍎 Food Diary",
    "🏋️ Exercise Diary",
    "⚖️ Weight Log",
    "📋 Copy Entries",
    "📅 History",
])


# ============================================================
# TAB 1: FOOD (add + diary)
# ============================================================
with tab_food:
    st.header("🍎 Food Diary")
    st.subheader("➕ Add Food")

    food_method = st.radio(
        "Choose how to add food",
        ["Search USDA Food Database", "Enter Food Manually"],
        horizontal=True,
        key="food_entry_method"
    )

    if food_method == "Search USDA Food Database":
        food_query = st.text_input(
            "Search food",
            placeholder="Example: apple, egg, banana, cooked rice",
            key="usda_query"
        )

        if len(food_query.strip()) >= 2:
            if not usda_api_key:
                st.info("Enter your USDA API key in the sidebar to search.")
            else:
                with st.spinner("Searching USDA FoodData Central..."):
                    try:
                        foods, api_error = search_food_api(
                            food_query.strip(), usda_api_key
                        )
                    except Exception as exc:
                        foods, api_error = [], str(exc)

                if api_error:
                    st.error(api_error)
                elif foods:
                    labels = [
                        f"{f['name']} | {f['brand'] or 'Generic'} | "
                        f"{f['calories']:.1f} kcal / 100 g | "
                        f"P {f['protein']:.1f} · F {f['fat']:.1f} · C {f['carbs']:.1f} g"
                        for f in foods
                    ]
                    selected_index = st.selectbox(
                        "Select a food",
                        range(len(foods)),
                        format_func=lambda i: labels[i],
                        key="usda_selected_index"
                    )

                    if st.button(
                        "Use selected USDA food", key="use_usda_food"
                    ):
                        st.session_state.selected_food = {
                            **foods[selected_index],
                            "source": "USDA"
                        }
                        st.rerun()
                else:
                    st.warning(
                        "No matching foods with calorie information were found."
                    )

    else:
        st.write(
            "Add homemade food or any item not found in the USDA database."
        )

        manual_cal_mode = st.radio(
            "How do you want to enter the calories?",
            ["Per 100 g", "Actual calories (no quantity needed)"],
            horizontal=True,
            key="manual_cal_mode"
        )

        if manual_cal_mode == "Per 100 g":
            with st.form("manual_food_form", clear_on_submit=False):
                manual_name = st.text_input(
                    "Food name",
                    placeholder="Example: Homemade paneer curry"
                )
                manual_calories = st.number_input(
                    "Calories per 100 grams (kcal)",
                    min_value=0.0,
                    max_value=10000.0,
                    value=150.0,
                    step=1.0
                )
                mp_col, mf_col, mc_col = st.columns(3)
                with mp_col:
                    manual_protein = st.number_input(
                        "Protein per 100 g (g)",
                        min_value=0.0,
                        max_value=100.0,
                        value=0.0,
                        step=0.5
                    )
                with mf_col:
                    manual_fat = st.number_input(
                        "Fat per 100 g (g)",
                        min_value=0.0,
                        max_value=100.0,
                        value=0.0,
                        step=0.5
                    )
                with mc_col:
                    manual_carbs = st.number_input(
                        "Carbs per 100 g (g)",
                        min_value=0.0,
                        max_value=100.0,
                        value=0.0,
                        step=0.5
                    )
                manual_submit = st.form_submit_button(
                    "Continue to quantity"
                )

            if manual_submit:
                if not manual_name.strip():
                    st.error("Please enter a food name.")
                else:
                    st.session_state.selected_food = {
                        "name": manual_name.strip(),
                        "calories": float(manual_calories),
                        "protein": float(manual_protein),
                        "fat": float(manual_fat),
                        "carbs": float(manual_carbs),
                        "brand": "Manual entry",
                        "serving_weight": None,
                        "serving_size": "User entered",
                        "source": "Manual"
                    }
                    st.rerun()

        else:
            st.caption(
                "Enter the actual total calories for what you ate. "
                "No quantity is needed — the entry is added directly to "
                "your diary. Protein, fat and carbs are optional totals in grams."
            )
            with st.form("manual_actual_food_form", clear_on_submit=True):
                actual_name = st.text_input(
                    "Food name",
                    placeholder="Example: Restaurant paneer wrap"
                )
                actual_calories = st.number_input(
                    "Actual calories (kcal)",
                    min_value=0.0,
                    max_value=100000.0,
                    value=150.0,
                    step=1.0
                )
                ap_col, af_col, ac_col = st.columns(3)
                with ap_col:
                    actual_protein = st.number_input(
                        "Protein (g, total)",
                        min_value=0.0,
                        max_value=10000.0,
                        value=0.0,
                        step=0.5
                    )
                with af_col:
                    actual_fat = st.number_input(
                        "Fat (g, total)",
                        min_value=0.0,
                        max_value=10000.0,
                        value=0.0,
                        step=0.5
                    )
                with ac_col:
                    actual_carbs = st.number_input(
                        "Carbs (g, total)",
                        min_value=0.0,
                        max_value=10000.0,
                        value=0.0,
                        step=0.5
                    )
                actual_submit = st.form_submit_button(
                    "➕ Add food to diary", type="primary"
                )

            if actual_submit:
                if not actual_name.strip():
                    st.error("Please enter a food name.")
                else:
                    try:
                        add_food_actual(
                            user_id, actual_name, actual_calories,
                            actual_protein, actual_fat, actual_carbs
                        )
                        st.session_state.selected_food = None
                        st.rerun()
                    except (ValueError, psycopg2.Error) as exc:
                        st.error(f"Could not add food: {exc}")

    selected_food = st.session_state.selected_food

    if selected_food is not None:
        st.divider()
        st.markdown(f"**Selected food:** {selected_food['name']}")
        st.caption(
            f"{selected_food['calories']:.1f} kcal per 100 g · "
            f"Protein {selected_food.get('protein', 0.0):.1f} g · "
            f"Fat {selected_food.get('fat', 0.0):.1f} g · "
            f"Carbs {selected_food.get('carbs', 0.0):.1f} g per 100 g · "
            f"{selected_food.get('source', 'Manual')}"
        )

        quantity_type = st.radio(
            "Quantity unit",
            ["Grams (g)", "Units (pieces)"],
            horizontal=True,
            key="add_quantity_type"
        )

        if quantity_type == "Grams (g)":
            quantity_g = st.number_input(
                "Quantity in grams",
                min_value=1.0,
                max_value=10000.0,
                value=100.0,
                step=10.0,
                key="add_quantity_grams"
            )
            unit_count = 0.0
            unit_weight = 0.0
        else:
            unit_count = st.number_input(
                "Number of pieces",
                min_value=1.0,
                max_value=1000.0,
                value=1.0,
                step=1.0,
                key="add_unit_count"
            )
            default_weight = selected_food.get("serving_weight") or 100
            unit_weight = st.number_input(
                "Weight of one piece (grams)",
                min_value=1.0,
                max_value=5000.0,
                value=float(default_weight),
                step=1.0,
                key="add_unit_weight"
            )
            quantity_g = unit_count * unit_weight

        calculated_food_calories = (
            selected_food["calories"] * quantity_g / 100
        )
        calculated_protein = selected_food.get("protein", 0.0) * quantity_g / 100
        calculated_fat = selected_food.get("fat", 0.0) * quantity_g / 100
        calculated_carbs = selected_food.get("carbs", 0.0) * quantity_g / 100

        fa, fb = st.columns(2)
        fa.metric("Total quantity", f"{quantity_g:.1f} g")
        fb.metric(
            "Calories for this quantity",
            f"{calculated_food_calories:.1f} kcal"
        )
        fc, fd, fe = st.columns(3)
        fc.metric("Protein", f"{calculated_protein:.1f} g")
        fd.metric("Fat", f"{calculated_fat:.1f} g")
        fe.metric("Carbs", f"{calculated_carbs:.1f} g")

        food_add_col, food_clear_col = st.columns(2)

        with food_add_col:
            if st.button(
                "➕ Add food to diary",
                type="primary",
                use_container_width=True
            ):
                try:
                    add_food(
                        user_id=user_id,
                        food_name=selected_food["name"],
                        calories_per_100g=selected_food["calories"],
                        quantity_g=quantity_g,
                        quantity_type=quantity_type,
                        unit_count=unit_count,
                        unit_weight=unit_weight,
                        source=selected_food.get("source", "Manual"),
                        protein_per_100g=selected_food.get("protein", 0.0),
                        fat_per_100g=selected_food.get("fat", 0.0),
                        carbs_per_100g=selected_food.get("carbs", 0.0)
                    )
                    st.session_state.selected_food = None
                    st.success("Food added to your diary.")
                    st.rerun()
                except (ValueError, psycopg2.Error) as exc:
                    st.error(f"Could not add food: {exc}")

        with food_clear_col:
            if st.button(
                "Clear selected food", use_container_width=True
            ):
                st.session_state.selected_food = None
                st.rerun()

    # --------------------------------------------------------
    # FOOD DIARY - VIEW / EDIT / DELETE
    # --------------------------------------------------------
    st.divider()
    st.subheader("📋 Food Diary")

    food_diary_day = st.date_input(
        "Food diary date",
        value=date.today(),
        key="food_diary_day"
    )
    food_entries = get_food_entries(user_id, food_diary_day)

    if food_entries:
        st.metric(
            f"Food calories on {food_diary_day.strftime('%d %b %Y')}",
            f"{sum(float(e['calories']) for e in food_entries):.1f} kcal"
        )
        dm1, dm2, dm3 = st.columns(3)
        dm1.metric(
            "Protein",
            f"{sum(float(e.get('protein_g') or 0) for e in food_entries):.1f} g"
        )
        dm2.metric(
            "Fat",
            f"{sum(float(e.get('fat_g') or 0) for e in food_entries):.1f} g"
        )
        dm3.metric(
            "Carbs",
            f"{sum(float(e.get('carbs_g') or 0) for e in food_entries):.1f} g"
        )

        for entry in food_entries:
            is_actual = entry["quantity_type"] == ACTUAL_CAL_TYPE
            if is_actual:
                title = (
                    f"{entry['food_name']} — actual calories — "
                    f"{entry['calories']:.1f} kcal"
                )
            else:
                title = (
                    f"{entry['food_name']} — {entry['quantity_g']:.0f} g — "
                    f"{entry['calories']:.1f} kcal"
                )

            with st.expander(title):
                st.caption(
                    f"Source: {entry['source']} · Added: "
                    f"{entry['created_at'][:16].replace('T', ' ')}"
                )
                st.write(
                    f"**Protein:** {float(entry.get('protein_g') or 0):.1f} g · "
                    f"**Fat:** {float(entry.get('fat_g') or 0):.1f} g · "
                    f"**Carbs:** {float(entry.get('carbs_g') or 0):.1f} g"
                )

                if is_actual:
                    # Entry holds actual totals, not per-100 g values.
                    with st.form(f"edit_food_actual_form_{entry['id']}"):
                        edit_actual_cal = st.number_input(
                            "Actual calories (kcal)",
                            min_value=0.0,
                            max_value=100000.0,
                            value=float(entry["calories"]),
                            step=1.0,
                            key=f"edit_actual_cal_{entry['id']}"
                        )
                        ea1, ea2, ea3 = st.columns(3)
                        with ea1:
                            edit_actual_p = st.number_input(
                                "Protein (g, total)",
                                min_value=0.0,
                                max_value=10000.0,
                                value=float(entry.get("protein_g") or 0),
                                step=0.5,
                                key=f"edit_actual_p_{entry['id']}"
                            )
                        with ea2:
                            edit_actual_f = st.number_input(
                                "Fat (g, total)",
                                min_value=0.0,
                                max_value=10000.0,
                                value=float(entry.get("fat_g") or 0),
                                step=0.5,
                                key=f"edit_actual_f_{entry['id']}"
                            )
                        with ea3:
                            edit_actual_c = st.number_input(
                                "Carbs (g, total)",
                                min_value=0.0,
                                max_value=10000.0,
                                value=float(entry.get("carbs_g") or 0),
                                step=0.5,
                                key=f"edit_actual_c_{entry['id']}"
                            )
                        save_actual_edit = st.form_submit_button(
                            "Save changes"
                        )

                    if save_actual_edit:
                        try:
                            update_food_actual(
                                user_id, entry["id"], edit_actual_cal,
                                edit_actual_p, edit_actual_f, edit_actual_c
                            )
                            st.success("Food entry updated.")
                            st.rerun()
                        except (ValueError, psycopg2.Error) as exc:
                            st.error(f"Could not update entry: {exc}")

                else:
                    with st.form(f"edit_food_form_{entry['id']}"):
                        edit_quantity = st.number_input(
                            "Edit quantity (grams)",
                            min_value=0.1,
                            max_value=10000.0,
                            value=float(entry["quantity_g"]),
                            step=1.0,
                            key=f"edit_food_qty_{entry['id']}"
                        )

                        edit_type = st.selectbox(
                            "Quantity type",
                            ["Grams (g)", "Units (pieces)"],
                            index=(
                                0 if entry["quantity_type"] == "Grams (g)"
                                else 1
                            ),
                            key=f"edit_food_type_{entry['id']}"
                        )

                        edit_count = st.number_input(
                            "Number of pieces (if applicable)",
                            min_value=0.0,
                            max_value=1000.0,
                            value=float(entry["unit_count"]),
                            step=1.0,
                            key=f"edit_food_count_{entry['id']}"
                        )

                        edit_weight = st.number_input(
                            "Weight per piece in grams (if applicable)",
                            min_value=0.0,
                            max_value=5000.0,
                            value=float(entry["unit_weight"]),
                            step=1.0,
                            key=f"edit_food_weight_{entry['id']}"
                        )

                        st.caption(
                            "Macros per 100 g (use this to fill in protein, fat and "
                            "carbs for entries logged before macros were tracked)."
                        )
                        em1, em2, em3 = st.columns(3)
                        with em1:
                            edit_protein100 = st.number_input(
                                "Protein / 100 g",
                                min_value=0.0,
                                max_value=100.0,
                                value=float(entry.get("protein_per_100g") or 0),
                                step=0.5,
                                key=f"edit_food_protein_{entry['id']}"
                            )
                        with em2:
                            edit_fat100 = st.number_input(
                                "Fat / 100 g",
                                min_value=0.0,
                                max_value=100.0,
                                value=float(entry.get("fat_per_100g") or 0),
                                step=0.5,
                                key=f"edit_food_fat_{entry['id']}"
                            )
                        with em3:
                            edit_carbs100 = st.number_input(
                                "Carbs / 100 g",
                                min_value=0.0,
                                max_value=100.0,
                                value=float(entry.get("carbs_per_100g") or 0),
                                step=0.5,
                                key=f"edit_food_carbs_{entry['id']}"
                            )

                        save_food_edit = st.form_submit_button(
                            "Save quantity changes"
                        )

                    if save_food_edit:
                        if edit_type == "Units (pieces)":
                            if edit_count <= 0 or edit_weight <= 0:
                                st.error(
                                    "Enter a positive piece count and piece weight."
                                )
                            else:
                                final_qty = edit_count * edit_weight
                                update_food(
                                    user_id, entry["id"], final_qty,
                                    edit_type, edit_count, edit_weight,
                                    edit_protein100, edit_fat100, edit_carbs100
                                )
                                st.success("Food quantity updated.")
                                st.rerun()
                        else:
                            update_food(
                                user_id, entry["id"], edit_quantity,
                                edit_type, 0, 0,
                                edit_protein100, edit_fat100, edit_carbs100
                            )
                            st.success("Food quantity updated.")
                            st.rerun()

                copy_food_date = st.date_input(
                    "Copy this food entry to date",
                    value=food_diary_day + timedelta(days=1),
                    key=f"copy_food_date_{entry['id']}"
                )
                if st.button(
                    "📄 Copy this food entry",
                    key=f"copy_food_{entry['id']}"
                ):
                    if copy_food_date == food_diary_day:
                        st.error("Choose a different destination date.")
                    elif copy_food_entry(user_id, entry["id"], copy_food_date):
                        st.success(f"Food entry copied to {copy_food_date.strftime('%d %b %Y')}.")
                        st.rerun()
                    else:
                        st.error("Could not find this food entry to copy.")

                if st.button(
                    "🗑️ Delete food entry",
                    key=f"delete_food_{entry['id']}"
                ):
                    delete_food(user_id, entry["id"])
                    st.success("Food entry deleted.")
                    st.rerun()
    else:
        st.info("No food entries for this date.")


# ============================================================
# TAB 2: EXERCISE (add + diary)
# ============================================================
with tab_exercise:
    st.header("🏋️ Exercise Diary")
    st.subheader("➕ Add Exercise")

    exercise_mode = st.radio(
        "How would you like to add exercise?",
        [
            "Search API Ninjas",
            "Enter Exercise Manually"
        ],
        horizontal=True,
        key="exercise_mode"
    )

    if exercise_mode == "Search API Ninjas":
        if not ninjas_api_key:
            st.info(
                "Enter your API Ninjas key in the sidebar to search "
                "exercise names and estimate calories burned."
            )
        else:
            exercise_category = st.radio(
                "Exercise category",
                ["Strength Training", "Cardio"],
                horizontal=True,
                key="exercise_category"
            )

            search_term = st.text_input(
                "Search exercise",
                placeholder=(
                    "Examples: bench press, squat, bicep curl, "
                    "running, cycling, treadmill"
                ),
                key="exercise_search_term"
            )

            if len(search_term.strip()) >= 2:
                api_type = (
                    "strength"
                    if exercise_category == "Strength Training"
                    else "cardio"
                )

                with st.spinner("Searching API Ninjas exercise database..."):
                    try:
                        exercise_results = search_ninjas_exercises(
                            search_term.strip(),
                            api_type,
                            ninjas_api_key
                        )
                        exercise_search_error = None
                    except requests.exceptions.HTTPError as exc:
                        status = (
                            exc.response.status_code
                            if exc.response is not None else None
                        )
                        exercise_results = []
                        if status in (401, 403):
                            exercise_search_error = (
                                "API Ninjas key is invalid or this endpoint "
                                "is not enabled for your plan."
                            )
                        else:
                            exercise_search_error = f"API error: {exc}"
                    except Exception as exc:
                        exercise_results = []
                        exercise_search_error = str(exc)

                if exercise_search_error:
                    st.error(exercise_search_error)
                elif exercise_results:
                    exercise_labels = [
                        (
                            f"{item.get('name', 'Unknown')} | "
                            f"{item.get('muscle', 'N/A')} | "
                            f"{item.get('difficulty', 'N/A')}"
                        )
                        for item in exercise_results
                    ]

                    chosen_exercise_index = st.selectbox(
                        "Select matching exercise",
                        range(len(exercise_results)),
                        format_func=lambda i: exercise_labels[i],
                        key="chosen_api_exercise"
                    )
                    chosen_exercise = exercise_results[
                        chosen_exercise_index
                    ]
                    chosen_exercise_name = chosen_exercise.get(
                        "name", search_term.strip()
                    )

                    with st.expander("Exercise instructions and details"):
                        st.write(
                            f"**Target muscle:** "
                            f"{chosen_exercise.get('muscle', 'Not specified')}"
                        )
                        st.write(
                            f"**Difficulty:** "
                            f"{chosen_exercise.get('difficulty', 'Not specified')}"
                        )
                        equipment = chosen_exercise.get("equipments", [])
                        if equipment:
                            st.write(
                                "**Equipment:** " + ", ".join(equipment)
                            )
                        if chosen_exercise.get("instructions"):
                            st.write(chosen_exercise["instructions"])
                        if chosen_exercise.get("safety_info"):
                            st.info(chosen_exercise["safety_info"])

                    st.markdown(f"**Selected exercise:** {chosen_exercise_name}")

                    body_weight_kg = st.number_input(
                        "Your body weight (kg) — used for calorie estimate",
                        min_value=20.0,
                        max_value=300.0,
                        value=78.0,
                        step=0.5,
                        key="api_body_weight"
                    )

                    if exercise_category == "Strength Training":
                        st.caption(
                            "Record the resistance/load, sets and reps below. "
                            "API Ninjas estimates calorie burn using body weight "
                            "and workout duration; lifted load and reps are "
                            "saved in your diary but are not inputs to its "
                            "calorie formula."
                        )
                        s1, s2, s3 = st.columns(3)
                        with s1:
                            lifted_weight_kg = st.number_input(
                                "Weight lifted (kg)",
                                min_value=0.0,
                                max_value=1000.0,
                                value=20.0,
                                step=1.0,
                                key="api_lifted_weight"
                            )
                        with s2:
                            sets_count = st.number_input(
                                "Sets",
                                min_value=1,
                                max_value=100,
                                value=3,
                                step=1,
                                key="api_strength_sets"
                            )
                        with s3:
                            reps_count = st.number_input(
                                "Reps per set",
                                min_value=1,
                                max_value=500,
                                value=12,
                                step=1,
                                key="api_strength_reps"
                            )

                        duration_minutes = st.number_input(
                            "Total workout duration (minutes, including rests)",
                            min_value=1,
                            max_value=600,
                            value=45,
                            step=5,
                            key="api_strength_duration"
                        )
                    else:
                        lifted_weight_kg = 0.0
                        sets_count = 0
                        reps_count = 0
                        duration_minutes = st.number_input(
                            "Cardio duration (minutes)",
                            min_value=1,
                            max_value=600,
                            value=30,
                            step=5,
                            key="api_cardio_duration"
                        )

                    if st.button(
                        "Calculate calories burned",
                        type="primary",
                        key="calculate_api_exercise"
                    ):
                        try:
                            with st.spinner(
                                "Calculating estimated calories burned..."
                            ):
                                estimate = estimate_ninjas_calories(
                                    chosen_exercise_name,
                                    body_weight_kg,
                                    duration_minutes,
                                    ninjas_api_key
                                )

                            st.session_state["pending_exercise"] = {
                                "exercise_name": estimate["matched_name"],
                                "category": exercise_category,
                                "duration_minutes": duration_minutes,
                                "body_weight_kg": body_weight_kg,
                                "lifted_weight_kg": lifted_weight_kg,
                                "sets": sets_count,
                                "reps": reps_count,
                                "calories_burned": estimate["calories"],
                                "source": "API Ninjas"
                            }
                        except requests.exceptions.HTTPError as exc:
                            status = (
                                exc.response.status_code
                                if exc.response is not None else None
                            )
                            if status in (401, 403):
                                st.error(
                                    "API Ninjas rejected the key or access "
                                    "to this endpoint."
                                )
                            elif status == 429:
                                st.error(
                                    "API Ninjas rate limit/quota reached. "
                                    "Try later or enter the exercise manually."
                                )
                            else:
                                st.error(f"API request failed: {exc}")
                        except Exception as exc:
                            st.error(f"Could not calculate calories: {exc}")

                    pending = st.session_state.get("pending_exercise")
                    if pending:
                        st.divider()
                        st.metric(
                            "Estimated calories burned",
                            f"{pending['calories_burned']:.0f} kcal"
                        )
                        st.caption(
                            f"API activity match: {pending['exercise_name']} · "
                            f"{pending['duration_minutes']} minutes"
                        )
                        save_col, cancel_col = st.columns(2)

                        with save_col:
                            if st.button(
                                "Save exercise to diary",
                                type="primary",
                                use_container_width=True,
                                key="save_api_exercise"
                            ):
                                try:
                                    add_exercise(
                                        user_id=user_id,
                                        exercise_name=pending["exercise_name"],
                                        category=pending["category"],
                                        duration_minutes=pending["duration_minutes"],
                                        body_weight_kg=pending["body_weight_kg"],
                                        lifted_weight_kg=pending["lifted_weight_kg"],
                                        sets=pending["sets"],
                                        reps=pending["reps"],
                                        calories_burned=pending["calories_burned"],
                                        source=pending["source"]
                                    )
                                    del st.session_state["pending_exercise"]
                                    st.success("Exercise saved to your diary.")
                                    st.rerun()
                                except Exception as exc:
                                    st.error(f"Could not save exercise: {exc}")

                        with cancel_col:
                            if st.button(
                                "Discard estimate",
                                use_container_width=True,
                                key="discard_api_exercise"
                            ):
                                del st.session_state["pending_exercise"]
                                st.rerun()

                else:
                    st.warning(
                        "No matching exercise found. Try a shorter or more "
                        "general search term, or use manual entry."
                    )

            else:
                st.caption(
                    "Type at least two characters to search the API Ninjas "
                    "exercise catalogue."
                )

    else:
        st.write(
            "Use this option if an exercise is unavailable through the API, "
            "or if you have a calorie value from a watch or another source."
        )

        with st.form("manual_exercise_form"):
            manual_exercise_name = st.text_input(
                "Exercise name",
                placeholder="Example: Barbell squat, treadmill walk"
            )
            manual_category = st.selectbox(
                "Category",
                ["Strength Training", "Cardio", "Sports", "Other"]
            )

            manual_body_weight = st.number_input(
                "Your body weight (kg)",
                min_value=0.0,
                max_value=300.0,
                value=78.0,
                step=0.5
            )

            manual_duration = st.number_input(
                "Duration (minutes)",
                min_value=0.0,
                max_value=1000.0,
                value=45.0,
                step=5.0
            )

            manual_lift_col1, manual_lift_col2, manual_lift_col3 = st.columns(3)
            with manual_lift_col1:
                manual_lifted_weight = st.number_input(
                    "Weight lifted (kg)",
                    min_value=0.0,
                    max_value=1000.0,
                    value=0.0,
                    step=1.0
                )
            with manual_lift_col2:
                manual_sets = st.number_input(
                    "Sets",
                    min_value=0,
                    max_value=100,
                    value=0,
                    step=1
                )
            with manual_lift_col3:
                manual_reps = st.number_input(
                    "Reps per set",
                    min_value=0,
                    max_value=500,
                    value=0,
                    step=1
                )

            manual_burned = st.number_input(
                "Calories burned (kcal)",
                min_value=0.0,
                max_value=10000.0,
                value=100.0,
                step=5.0
            )

            manual_exercise_submit = st.form_submit_button(
                "Save manual exercise", type="primary"
            )

        if manual_exercise_submit:
            if not manual_exercise_name.strip():
                st.error("Please enter an exercise name.")
            elif manual_burned < 0:
                st.error("Calories burned cannot be negative.")
            else:
                try:
                    add_exercise(
                        user_id=user_id,
                        exercise_name=manual_exercise_name,
                        category=manual_category,
                        duration_minutes=manual_duration,
                        body_weight_kg=manual_body_weight,
                        lifted_weight_kg=manual_lifted_weight,
                        sets=manual_sets,
                        reps=manual_reps,
                        calories_burned=manual_burned,
                        source="Manual"
                    )
                    st.success("Manual exercise saved.")
                    st.rerun()
                except Exception as exc:
                    st.error(f"Could not save exercise: {exc}")

    # --------------------------------------------------------
    # EXERCISE DIARY - VIEW / DELETE
    # --------------------------------------------------------
    st.divider()
    st.subheader("🏃 Exercise Diary")

    exercise_diary_day = st.date_input(
        "Exercise diary date",
        value=date.today(),
        key="exercise_diary_day"
    )
    exercise_entries = get_exercise_entries(
        user_id, exercise_diary_day
    )

    if exercise_entries:
        st.metric(
            f"Exercise calories on {exercise_diary_day.strftime('%d %b %Y')}",
            f"{sum(float(e['calories_burned']) for e in exercise_entries):.1f} kcal"
        )

        for entry in exercise_entries:
            title = (
                f"{entry['exercise_name']} — "
                f"{entry['calories_burned']:.1f} kcal burned"
            )

            with st.expander(title):
                st.write(f"**Category:** {entry['category']}")
                st.write(
                    f"**Duration:** {entry['duration_minutes']:.0f} minutes"
                )
                st.write(
                    f"**Body weight used for estimate:** "
                    f"{entry['body_weight_kg']:.1f} kg"
                )

                if entry["category"] == "Strength Training":
                    st.write(
                        f"**Weight lifted:** {entry['lifted_weight_kg']:.1f} kg"
                    )
                    st.write(
                        f"**Sets × reps:** {entry['sets']} × {entry['reps']}"
                    )

                st.write(f"**Source:** {entry['source']}")
                st.caption(
                    f"Added: {entry['created_at'][:16].replace('T', ' ')}"
                )

                copy_exercise_date = st.date_input(
                    "Copy this exercise entry to date",
                    value=exercise_diary_day + timedelta(days=1),
                    key=f"copy_exercise_date_{entry['id']}"
                )
                if st.button(
                    "📄 Copy this exercise entry",
                    key=f"copy_exercise_{entry['id']}"
                ):
                    if copy_exercise_date == exercise_diary_day:
                        st.error("Choose a different destination date.")
                    elif copy_exercise_entry(user_id, entry["id"], copy_exercise_date):
                        st.success(f"Exercise entry copied to {copy_exercise_date.strftime('%d %b %Y')}.")
                        st.rerun()
                    else:
                        st.error("Could not find this exercise entry to copy.")

                if st.button(
                    "🗑️ Delete exercise entry",
                    key=f"delete_exercise_{entry['id']}"
                ):
                    delete_exercise(user_id, entry["id"])
                    st.success("Exercise entry deleted.")
                    st.rerun()
    else:
        st.info("No exercise entries for this date.")


# ============================================================
# TAB 3: WEIGHT LOG
# ============================================================
with tab_weight:
    st.header("⚖️ Weight Log")
    st.caption("Record your body weight over time. These records are separate from the weight used by the exercise calorie estimator.")
    with st.form("add_weight_form", clear_on_submit=True):
        weight_col1, weight_col2 = st.columns(2)
        with weight_col1:
            new_weight = st.number_input("Weight (kg)", min_value=1.0, max_value=500.0, value=84.0, step=0.1)
        with weight_col2:
            weight_day = st.date_input("Date", value=date.today())
        weight_notes = st.text_input("Notes (optional)", placeholder="Morning, before breakfast, etc.")
        weight_submit = st.form_submit_button("Save weight", type="primary")
    if weight_submit:
        try:
            add_weight(user_id, new_weight, weight_day, weight_notes)
            st.success("Weight saved.")
            st.rerun()
        except Exception as exc:
            st.error(f"Could not save weight: {exc}")

    weight_rows = get_weights(user_id)
    if weight_rows:
        weight_df = pd.DataFrame(weight_rows)
        weight_df["entry_date"] = pd.to_datetime(weight_df["entry_date"])
        chronological = weight_df.sort_values(["entry_date", "id"])
        first_weight = float(chronological.iloc[0]["weight_kg"])
        latest_weight = float(chronological.iloc[-1]["weight_kg"])
        lowest_weight = float(weight_df["weight_kg"].min())
        wc1, wc2, wc3 = st.columns(3)
        wc1.metric("Latest weight", f"{latest_weight:.1f} kg")
        wc2.metric("Change since first log", f"{latest_weight-first_weight:+.1f} kg")
        wc3.metric("Lowest recorded", f"{lowest_weight:.1f} kg")
        chart = chronological.set_index("entry_date")[["weight_kg"]]
        st.line_chart(chart)
        st.subheader("Weight history records")
        for wr in weight_rows:
            weight_date = wr["entry_date"]
            with st.expander(f"{weight_date.strftime('%d %b %Y')} — {float(wr['weight_kg']):.1f} kg"):
                with st.form(f"edit_weight_{wr['id']}"):
                    edit_w1, edit_w2 = st.columns(2)
                    with edit_w1:
                        edited_weight = st.number_input("Weight (kg)", min_value=1.0, max_value=500.0, value=float(wr["weight_kg"]), step=0.1, key=f"weight_value_{wr['id']}")
                    with edit_w2:
                        edited_day = st.date_input("Date", value=weight_date, key=f"weight_date_{wr['id']}")
                    edited_notes = st.text_input("Notes", value=wr["notes"] or "", key=f"weight_notes_{wr['id']}")
                    save_weight = st.form_submit_button("Save changes")
                if save_weight:
                    update_weight(user_id, wr["id"], edited_weight, edited_day, edited_notes)
                    st.success("Weight record updated.")
                    st.rerun()
                if st.button("Delete weight record", key=f"delete_weight_{wr['id']}"):
                    delete_weight(user_id, wr["id"])
                    st.success("Weight record deleted.")
                    st.rerun()
    else:
        st.info("No weight records yet. Add your first measurement above.")


# ============================================================
# TAB 4: COPY FOOD + EXERCISE ENTRIES BETWEEN DATES
# ============================================================
with tab_copy:
    st.subheader("📋 Copy Entries to Another Date")
    st.caption("Copies all food and exercise entries from the selected source date. Original entries remain unchanged.")
    with st.form("copy_entries_form"):
        copy_source_day = st.date_input("Copy entries from", value=date.today(), key="copy_source_day")
        copy_destination_day = st.date_input("Copy entries to", value=date.today() + timedelta(days=1), key="copy_destination_day")
        copy_confirm = st.checkbox("I understand this will add duplicate entries to the destination date.")
        copy_submit = st.form_submit_button("Copy food and exercise entries", type="primary")
    if copy_submit:
        if not copy_confirm:
            st.warning("Please confirm before copying.")
        elif copy_source_day == copy_destination_day:
            st.error("Choose two different dates.")
        else:
            try:
                food_copied, exercise_copied = copy_day_entries(user_id, copy_source_day, copy_destination_day)
                st.success(f"Copied {food_copied} food entries and {exercise_copied} exercise entries to {copy_destination_day.strftime('%d %b %Y')}. Originals were kept.")
                st.rerun()
            except Exception as exc:
                st.error(f"Could not copy entries: {exc}")


# ============================================================
# TAB 5: COMBINED HISTORY
# ============================================================
with tab_history:
    st.subheader("📅 Combined Calorie History — Last 10 Days")

    history = get_history(user_id, days=10)

    if history:
        history_df = pd.DataFrame(history)
        for col in [
            "Maintenance calories", "Calories consumed", "Calories burned",
            "Current weight (kg)", "Deficit / surplus",
            "Protein (g)", "Fat (g)", "Carbs (g)"
        ]:
            history_df[col] = pd.to_numeric(history_df[col], errors="coerce").round(1)

        st.dataframe(
            history_df,
            use_container_width=True,
            hide_index=True
        )

        chart_df = history_df.set_index("Date")[
            ["Maintenance calories", "Calories consumed", "Calories burned", "Deficit / surplus"]
        ]
        st.bar_chart(chart_df)

        st.caption("Daily macronutrients (g)")
        macro_chart_df = history_df.set_index("Date")[
            ["Protein (g)", "Fat (g)", "Carbs (g)"]
        ]
        st.bar_chart(macro_chart_df)
    else:
        st.info("Your combined food and exercise history will appear here.")


# ============================================================
# FOOTER
# ============================================================
st.divider()
st.caption(
    "Food and exercise records are stored separately for each account "
    "in Supabase PostgreSQL. Food values are estimates. Exercise calories "
    "from API Ninjas are estimates, not direct measurements. Strength "
    "training load, sets and reps are recorded, but the API calorie "
    "estimate is based on body weight and session duration."
)
