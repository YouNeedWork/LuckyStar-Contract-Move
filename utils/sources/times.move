module utils::times {
    const SECOND_IN_MILLISECONDS: u64 = 1000;
    const MINUTE_IN_MILLISECONDS: u64 = 1000 * 60;
    const HOUR_IN_MILLISECONDS: u64 = 1000 * 60 * 60;
    const DAY_IN_MILLISECONDS: u64 = 1000 * 60 * 60 * 24;
    const WEEK_IN_MILLISECONDS: u64 = 1000 * 60 * 60 * 24 * 7;

    const SECOND_IN_SECONDS: u64 = 1;
    const MINUTE_IN_SECONDS: u64 = 1 * 60;
    const HOUR_IN_SECONDS: u64 = 1 * 60 * 60;
    const DAY_IN_SECONDS: u64 = 1 * 60 * 60 * 24;
    const WEEK_IN_SECONDS: u64 = 1 * 60 * 60 * 24 * 7;

    public fun days_in_milliseconds(days: u64): u64 {
        DAY_IN_MILLISECONDS * days
    }

    public fun hours_in_milliseconds(hours: u64): u64 {
        HOUR_IN_MILLISECONDS * hours
    }

    public fun minutes_in_milliseconds(minutes: u64): u64 {
        MINUTE_IN_MILLISECONDS * minutes
    }

    public fun seconds_in_milliseconds(seconds: u64): u64 {
        SECOND_IN_MILLISECONDS * seconds
    }

    public fun weeks_in_milliseconds(week: u64): u64 {
        WEEK_IN_MILLISECONDS * week
    }

    public fun days(days: u64): u64 {
        DAY_IN_SECONDS * days
    }

    public fun hours(hours: u64): u64 {
        HOUR_IN_SECONDS * hours
    }

    public fun seconds(seconds: u64): u64 {
        SECOND_IN_SECONDS * seconds
    }

    public fun weeks(week: u64): u64 {
        WEEK_IN_SECONDS * week
    }

    public fun minutes(minutes: u64): u64 {
        MINUTE_IN_SECONDS * minutes
    }
}