module staking::staking {
    use std::debug::print;

    use admin::admin::{is_admin, Manage};
    use token::nonTransferCoin::{Self, NonTransferCoin};
    use utils::utils;

    use staking::luck_vault::{Self, Vault, LuckVault, RewardLuckVault};
    use sui::bag::{Self, Bag};
    use sui::clock::{timestamp_ms, Clock};
    use sui::coin::{Self, Coin};
    use sui::object::{Self, UID};
    use sui::pay;
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::{Self, TxContext};

    #[test_only]
    use luck::luck::LUCK;
    #[test_only]
    use std::vector;
    #[test_only]
    use sui::test_scenario::{Self, next_tx, Scenario};
    #[test_only]
    use sui::test_utils;
    #[test_only]
    use sui::sui::{SUI};
    #[test_only]
    use xluck::xLuck::{Self, XLUCK};

    const DECIMAL:u64 = 1000000000;

    const EUserCanNotUnStake: u64 = 1008;
    const EUserNotStake: u64 = 1009;
    const EUserNotHaveEnoughStakeAmount: u64 = 1010;


    const ETimestampElapsed: u64 = 1002;
    const ENoStake: u64 = 1003;
    const EPoolEmergencyLocked: u64 = 1004;
    const ERequireAdminPermission: u64 = 1005;
    const EStakeValue: u64 = 1006;
    const EStakeAmount: u64 = 1007;
    const EAmountNotEnough: u64 = 1008;

    struct Pool<phantom REWARD, phantom EXT, phantom LUCK, phantom XLUCK, phantom ESLUCK> has key, store {
        id: UID,
        luck_coin: Coin<LUCK>,
        xluck_coin: NonTransferCoin<XLUCK>,
        esluck_coin: NonTransferCoin<ESLUCK>,

        esluck_reward_coin: NonTransferCoin<REWARD>,
        ext_reward_coin: Coin<EXT>,
        reward_per_sec: u64,
        ext_reward_per_sec: u64,

        accum_reward: u256,
        ext_accum_reward: u256,

        start_timestamp: u64,
        end_timestamp: u64,
        last_updated: u64,

        scale: u64,

        stakes: Bag,
        emergency_locked: bool,
        total_staked: u256,
        total_stakers: u256,
        total_rewards: u256,

        vest: NonTransferCoin<ESLUCK>,
        vest_duration: u64,
        vester: Bag,

        total_vest_amount: u256,
        total_vester: u256,
        total_vester_reward: u256,
    }

    struct UserVest has store {
        amount: u64,
        unobtainable_reward: u64,
        earned_reward: u64,
        lastet_updated: u64,
        passed_time: u64,
    }

    /// Stores user stake info.
    struct UserStake has store, drop {
        luck_amount: u64,
        xluck_amount: u64,
        esluck_amount: u64,
        unobtainable_reward: u64,
        earned_reward: u64,
        ext_earned_reward: u64,
        ext_unobtainable_reward: u64,

        earned_per_token_store: u64,
        ext_earned_per_token_store: u64,
    }

    public entry fun add_reward_coin<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        reward_coins: NonTransferCoin<REWARD>,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        nonTransferCoin::join(&mut pool.esluck_reward_coin, reward_coins)
    }

    public entry fun add_ext_reward_coin<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        ext_coin: Coin<EXT>,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        coin::join(&mut pool.ext_reward_coin, ext_coin)
    }


    public entry fun change_reward_per_sec<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        reward_per_sec: u64,
        scale: u64,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        pool.scale = scale;
        pool.reward_per_sec = reward_per_sec;
    }

    public entry fun change_ext_reward_per_sec<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        ext_reward_per_sec: u64,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        pool.ext_reward_per_sec = ext_reward_per_sec;
    }

    public entry fun change_vest_duration<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        duration: u64,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        pool.vest_duration = duration;
    }

    public entry fun create_stake_pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        adm: &mut Manage,
        reward_coins: NonTransferCoin<REWARD>,
        ext_reward_coin: Coin<EXT>,
        reward_per_sec: u64,
        ext_reward_per_sec: u64,
        scale: u64,
        vest_duration: u64,
        end_timestamp: u64,
        lock: &Clock,
        ctx: &mut TxContext,
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        let start_timestamp = timestamp_ms(lock);
        assert!(end_timestamp > start_timestamp, ETimestampElapsed);

        public_share_object(Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK> {
            id: object::new(ctx),
            luck_coin: coin::zero(ctx),
            xluck_coin: nonTransferCoin::zero(tx_context::sender(ctx), ctx),
            esluck_coin: nonTransferCoin::zero(tx_context::sender(ctx), ctx),
            esluck_reward_coin: reward_coins,
            ext_reward_coin,
            reward_per_sec,
            ext_reward_per_sec,
            start_timestamp,
            end_timestamp,
            last_updated: start_timestamp,
            accum_reward: 0,
            ext_accum_reward: 0,
            scale,
            stakes: bag::new(ctx),
            emergency_locked: false,
            total_staked: 0,
            total_stakers: 0,
            total_rewards: 0,
            vest: nonTransferCoin::zero<ESLUCK>(tx_context::sender(ctx), ctx),
            vest_duration,
            vester: bag::new(ctx),
            total_vest_amount: 0,
            total_vester: 0,
            total_vester_reward: 0,
        });
    }

    fun get_time_for_last_update<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        clock: &Clock
    ): u64 {
        if (pool.end_timestamp < timestamp_ms(clock)) {
            pool.end_timestamp
        } else {
            timestamp_ms(clock)
        }
    }

    fun update_accum_reward<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        clock: &Clock
    ) {
        let current_time = get_time_for_last_update(pool, clock);
        let (new_accum_rewards, new_ext_accum_rewards) = accum_rewards_since_last_updated(pool, current_time);

        pool.last_updated = current_time;
        if (new_accum_rewards != 0) {
            pool.accum_reward = pool.accum_reward + new_accum_rewards;
            pool.ext_accum_reward = pool.ext_accum_reward + new_ext_accum_rewards;
        };
    }

    public fun total_staked<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>
    ): u256 {
        (nonTransferCoin::value(&pool.esluck_coin) as u256) + (nonTransferCoin::value(
            &pool.xluck_coin
        ) as u256) + (coin::value(&pool.luck_coin) as u256)
    }

    fun accum_rewards_since_last_updated<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        current_time: u64
    ): (u256, u256) {
        let time_diff = (current_time - pool.last_updated) / 1000;
        let total_supply = total_staked(pool);

        if (total_supply == 0) {
            (0, 0)
        } else {
            print(&90999999999);
            print(&time_diff);
            print(&pool.reward_per_sec);
            print(&pool.scale);
            print(&total_supply);

            let reward_per_token = (time_diff as u256) * (pool.reward_per_sec as u256) * (pool.scale as u256) / (total_supply);
            let ext_reward_per_token = (time_diff as u256) * (pool.ext_reward_per_sec as u256) * (pool.scale as u256) / (total_supply);
            print(&reward_per_token);
            print(&ext_reward_per_token);
            (reward_per_token, ext_reward_per_token)
        }
    }

    fun update_user_earnings(
        accum_reward: u256,
        ext_accum_reward: u256,
        scale: u256,
        user_stake: &mut UserStake
    ) {
        let earned =
            user_earned_since_last_update(accum_reward, scale, user_stake);
        user_stake.earned_reward = user_stake.earned_reward + (earned as u64);
        user_stake.unobtainable_reward = user_stake.unobtainable_reward + (earned as u64);
        user_stake.earned_per_token_store = (accum_reward as u64);


        let ext_earned = ext_user_earned_since_last_update(ext_accum_reward, scale, user_stake);
        user_stake.ext_earned_reward = user_stake.ext_earned_reward + (ext_earned as u64);
        user_stake.ext_unobtainable_reward = user_stake.ext_unobtainable_reward + (ext_earned as u64);
        user_stake.ext_earned_per_token_store = (ext_accum_reward as u64);
    }

    fun user_earned_since_last_update(
        accum_reward: u256,
        scale: u256,
        user_stake: &UserStake
    ): u256 {
        let user_total_stake = (user_total_stake(
            user_stake.luck_amount,
            user_stake.xluck_amount,
            user_stake.esluck_amount
        ) as u256);
        //600/accum_reward
        user_total_stake * (accum_reward - (user_stake.earned_per_token_store as u256)) / scale
    }

    fun ext_user_earned_since_last_update(
        accum_reward: u256,
        scale: u256,
        user_stake: &UserStake
    ): u256 {
        let user_total_stake = (user_total_stake(
            user_stake.luck_amount,
            user_stake.xluck_amount,
            user_stake.esluck_amount
        ) as u256);

        user_total_stake * (accum_reward - (user_stake.ext_earned_per_token_store as u256)) / scale
    }

    public entry fun stake_luck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        c: vector<Coin<LUCK>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let paid = coin::zero<LUCK>(ctx);
        pay::join_vec(&mut paid, c);
        assert!(coin::value(&paid) >= amount, 1001);
        let sender = tx_context::sender(ctx);
        let stake_coin = coin::split(&mut paid, amount, ctx);
        utils::destroy_zero_or_transfer(paid, ctx);

        update_accum_reward(pool, clock);


        pool.total_staked = pool.total_staked + (amount as u256);
        if (bag::contains(&pool.stakes, sender)) {
            let user_stake = bag::remove<address, UserStake>(&mut pool.stakes, sender);

            update_user_earnings(
                pool.accum_reward,
                pool.ext_accum_reward,
                (pool.scale as u256),
                &mut user_stake
            );

            inner_claim(pool, &mut user_stake, ctx);
            user_stake.luck_amount = user_stake.luck_amount + amount;
            bag::add(&mut pool.stakes, sender, user_stake);
            coin::join(&mut pool.luck_coin, stake_coin);
        } else {
            bag::add(&mut pool.stakes, sender, UserStake {
                luck_amount: amount,
                xluck_amount: 0,
                esluck_amount: 0,
                unobtainable_reward: 0,
                earned_reward: 0,
                ext_earned_reward: 0,
                ext_unobtainable_reward: 0,
                earned_per_token_store: (pool.accum_reward as u64),
                ext_earned_per_token_store: (pool.ext_accum_reward as u64),
            });

            pool.total_stakers = pool.total_stakers + 1;
            coin::join(&mut pool.luck_coin, stake_coin);
        }
    }

    public fun get_reward_per_sec<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>
    ): u64 {
        pool.reward_per_sec
    }

    public entry fun stake_xluck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        c: vector<NonTransferCoin<XLUCK>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);

        let paid = nonTransferCoin::zero<XLUCK>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);


        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);

        update_accum_reward(pool, clock);
        pool.total_staked = pool.total_staked + (amount as u256);
        if (bag::contains(&pool.stakes, sender)) {
            let user_stake = bag::remove<address, UserStake>(&mut pool.stakes, sender);

            update_user_earnings(
                pool.accum_reward,
                pool.ext_accum_reward,
                (pool.scale as u256),
                &mut user_stake
            );

            inner_claim(pool, &mut user_stake, ctx);
            user_stake.xluck_amount = user_stake.xluck_amount + amount;
            bag::add(&mut pool.stakes, sender, user_stake);
            nonTransferCoin::join(&mut pool.xluck_coin, stake_coin);
        } else {
            bag::add(&mut pool.stakes, sender, UserStake {
                luck_amount: 0,
                xluck_amount: amount,
                esluck_amount: 0,
                unobtainable_reward: 0,
                earned_reward: 0,
                ext_unobtainable_reward: 0,
                ext_earned_reward: 0,
                earned_per_token_store: (pool.accum_reward as u64),
                ext_earned_per_token_store: (pool.ext_accum_reward as u64),
            });
            pool.total_stakers = pool.total_stakers + 1;
            nonTransferCoin::join(&mut pool.xluck_coin, stake_coin);
        }
    }

    public entry fun stake_esluck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        c: vector<NonTransferCoin<ESLUCK>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);

        let paid = nonTransferCoin::zero<ESLUCK>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);


        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);

        update_accum_reward(pool, clock);

        pool.total_staked = pool.total_staked + (amount as u256);
        if (bag::contains(&pool.stakes, sender)) {
            let user_stake = bag::remove<address, UserStake>(&mut pool.stakes, sender);

            update_user_earnings(
                pool.accum_reward,
                pool.ext_accum_reward,
                (pool.scale as u256),
                &mut user_stake
            );

            inner_claim(pool, &mut user_stake, ctx);
            user_stake.esluck_amount = user_stake.esluck_amount + amount;
            bag::add(&mut pool.stakes, sender, user_stake);
            nonTransferCoin::join(&mut pool.esluck_coin, stake_coin);
        } else {
            bag::add(&mut pool.stakes, sender, UserStake {
                luck_amount: 0,
                xluck_amount: 0,
                esluck_amount: amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                ext_unobtainable_reward: 0,
                ext_earned_reward: 0,
                earned_per_token_store: (pool.accum_reward as u64),
                ext_earned_per_token_store: (pool.ext_accum_reward as u64),
            });

            pool.total_stakers = pool.total_stakers + 1;

            nonTransferCoin::join(&mut pool.esluck_coin, stake_coin);
        }
    }

    public fun get_user_total_stake<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        ctx: &mut TxContext
    ): u64 {
        let sender = tx_context::sender(ctx);
        let user_stake = bag::borrow<address, UserStake>(&pool.stakes, sender);
        user_total_stake(user_stake.luck_amount, user_stake.xluck_amount, user_stake.esluck_amount)
    }

    fun user_total_stake(a: u64, b: u64, c: u64): u64 {
        a + b + c
    }

    public fun get_user_total_stake_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        ctx: &mut TxContext
    ): u64 {
        let user_stake = bag::borrow<address, UserStake>(&pool.stakes, tx_context::sender(ctx));
        let user_stake_amount = user_total_stake(
            user_stake.luck_amount,
            user_stake.xluck_amount,
            user_stake.esluck_amount
        );
        user_stake_amount
    }

    public entry fun unstake_luck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), ENoStake);
        update_accum_reward(pool, clock);
        let user_stake = bag::remove<address, UserStake>(&mut pool.stakes, sender);
        update_user_earnings(pool.accum_reward, pool.ext_accum_reward, (pool.scale as u256), &mut user_stake);


        check_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, &user_stake, amount, ctx);

        assert!(user_stake.luck_amount >= amount, EStakeAmount);
        user_stake.luck_amount = user_stake.luck_amount - amount;

        pool.total_staked = pool.total_staked - (amount as u256);
        let luck = coin::split(&mut pool.luck_coin, amount, ctx);
        public_transfer(luck, sender);
        inner_claim(pool, &mut user_stake, ctx);

        if (user_total_stake(user_stake.luck_amount, user_stake.xluck_amount, user_stake.esluck_amount) == 0) {
            safe_remove_user_stake(pool, user_stake);
        } else {
            bag::add(&mut pool.stakes, sender, user_stake);
        }
    }

    public entry fun unstake_xluck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), ENoStake);
        update_accum_reward(pool, clock);
        let user_stake = bag::remove(&mut pool.stakes, sender);
        update_user_earnings(pool.accum_reward, pool.ext_accum_reward, (pool.scale as u256), &mut user_stake);

        check_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, &user_stake, amount, ctx);

        assert!(user_stake.xluck_amount >= amount, EStakeAmount);
        user_stake.xluck_amount = user_stake.xluck_amount - amount;

        pool.total_staked = pool.total_staked - (amount as u256);
        let xluck_coin = nonTransferCoin::split(&mut pool.xluck_coin, sender, amount, ctx);
        public_transfer(xluck_coin, sender);
        inner_claim(pool, &mut user_stake, ctx);
        if (user_total_stake(user_stake.luck_amount, user_stake.xluck_amount, user_stake.esluck_amount) == 0) {
            safe_remove_user_stake(pool, user_stake);
        } else {
            bag::add(&mut pool.stakes, sender, user_stake);
        }
    }

    public entry fun unstake_esluck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), ENoStake);
        update_accum_reward(pool, clock);
        let user_stake = bag::remove(&mut pool.stakes, sender);
        update_user_earnings(pool.accum_reward, pool.ext_accum_reward, (pool.scale as u256), &mut user_stake);


        //let user_total_stake = user_total_stake(user_stake.luck_amount, user_stake.xluck_amount, user_stake.esluck_amount);
        check_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, &user_stake, amount, ctx);

        assert!(user_stake.esluck_amount >= amount, EStakeAmount);
        user_stake.esluck_amount = user_stake.esluck_amount - amount;

        pool.total_staked = pool.total_staked - (amount as u256);
        let esluck_coin = nonTransferCoin::split(&mut pool.esluck_coin, sender, amount, ctx);
        public_transfer(esluck_coin, sender);
        inner_claim(pool, &mut user_stake, ctx);
        if (user_total_stake(user_stake.luck_amount, user_stake.xluck_amount, user_stake.esluck_amount) == 0) {
            safe_remove_user_stake(pool, user_stake);
        } else {
            bag::add(&mut pool.stakes, sender, user_stake);
        }
    }

    fun get_user_vesting<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>, ctx: &mut TxContext): (u64, u64) {
        let sender = tx_context::sender(ctx);
        if (bag::contains(&pool.vester, sender)) {
            let user_stake = bag::borrow<address, UserVest>(&pool.vester, sender);

            print(&2222222222222);
            print(&user_stake.amount);
            print(user_stake);
            (user_stake.amount, pool.vest_duration - user_stake.passed_time)
        } else {
            (0, 0)
        }
    }

    fun check_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        user_stake: &UserStake,
        amount: u64,
        ctx: &mut TxContext)
    {
        let user_stake_amount = user_total_stake(
            user_stake.luck_amount,
            user_stake.xluck_amount,
            user_stake.esluck_amount
        );
        let (vesting_amount, time_left) = get_user_vesting<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, ctx);
        calculate_staker_can_unstake(
            vesting_amount,
            time_left,
            (pool.accum_reward as u64),
            user_stake_amount,
            amount
        );
    }

    fun check_deposit_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        user_stake: &UserStake,
        ctx: &mut TxContext)
    {
        let user_stake_amount = user_total_stake(
            user_stake.luck_amount,
            user_stake.xluck_amount,
            user_stake.esluck_amount
        );
        let (vesting_amount, time_left) = get_user_vesting<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, ctx);
        calculate_staker_need_stake(vesting_amount, time_left, (pool.accum_reward as u64), user_stake_amount);
    }


    public entry fun claim<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);

        assert!(bag::contains(&pool.stakes, sender), ENoStake);
        update_accum_reward(pool, clock);

        let user_stake = bag::remove(&mut pool.stakes, sender);
        update_user_earnings(pool.accum_reward, pool.ext_accum_reward, (pool.scale as u256), &mut user_stake);
        inner_claim(pool, &mut user_stake, ctx);
        if (user_total_stake(user_stake.luck_amount, user_stake.xluck_amount, user_stake.esluck_amount) == 0) {
            safe_remove_user_stake(pool, user_stake);
        } else {
            bag::add(&mut pool.stakes, sender, user_stake);
        }
    }

    fun safe_remove_user_stake<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        user_stake: UserStake
    ) {
        assert!(user_stake.xluck_amount == 0, EStakeValue);
        assert!(user_stake.esluck_amount == 0, EStakeValue);
        assert!(user_stake.luck_amount == 0, EStakeValue);
        assert!(user_stake.earned_reward == 0, EStakeValue);
        assert!(user_stake.ext_earned_reward == 0, EStakeValue);

        pool.total_stakers = pool.total_stakers - 1;
    }

    fun inner_claim<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        user_stake: &mut UserStake,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);

        let earned = user_stake.earned_reward;
        pool.total_rewards = pool.total_rewards + (earned as u256);
        let r_coin = nonTransferCoin::split(
            &mut pool.esluck_reward_coin,
            tx_context::sender(ctx),
            earned,
            ctx
        );

        public_transfer(r_coin, sender);

        let ext_r_coin = coin::split(
            &mut pool.ext_reward_coin,
            user_stake.ext_earned_reward,
            ctx
        );
        public_transfer(ext_r_coin, sender);

        user_stake.earned_reward = 0;
        user_stake.ext_earned_reward = 0;
    }

    public entry fun enable_emergency<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        adm: &mut Manage,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        pool.emergency_locked = true;
    }


    public entry fun deposit<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut Vault,
        c: vector<NonTransferCoin<ESLUCK>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), EUserNotStake);

        let paid = nonTransferCoin::zero<ESLUCK>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);
        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);


        if (bag::contains(&pool.vester, sender)) {
            let user_vest = bag::borrow_mut<address, UserVest>(&mut pool.vester, sender);
            update_user_vest_earnings(pool.vest_duration, user_vest, clock);
            inner_vest_claim(vau, user_vest, ctx);

            //restart when user deposit
            user_vest.amount = user_vest.amount + amount;
            user_vest.unobtainable_reward = 0;
            user_vest.lastet_updated = timestamp_ms(clock);
            user_vest.passed_time = 0;
            nonTransferCoin::join(&mut pool.vest, stake_coin);
        } else {
            bag::add(&mut pool.vester, sender, UserVest {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                lastet_updated: timestamp_ms(clock),
                passed_time: 0,
            });
            nonTransferCoin::join(&mut pool.vest, stake_coin);
            pool.total_vester = pool.total_vester + 1;
        };

        let user_stake = bag::borrow<address, UserStake>(&mut pool.stakes, sender);
        check_deposit_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, user_stake, ctx);
    }

    public entry fun withdraw<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut Vault,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vester, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vester, sender);
        update_user_vest_earnings(pool.vest_duration, &mut user_vest, clock);
        inner_vest_claim(vau, &mut user_vest, ctx);
        let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
        pool.total_vester = pool.total_vester - 1;

        let s_coin = nonTransferCoin::split(&mut pool.vest, sender, amount - unobtainable_reward, ctx);
        public_transfer(s_coin, sender);
    }

    public entry fun claim_vest<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut Vault,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);

        assert!(bag::contains(&pool.vester, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vester, sender);
        update_user_vest_earnings(pool.vest_duration, &mut user_vest, clock);
        inner_vest_claim(vau, &mut user_vest, ctx);
        print(&user_vest);

        if ((user_vest.amount - user_vest.unobtainable_reward) > 0) {
            bag::add(&mut pool.vester, sender, user_vest);
        } else {
            pool.total_vester = pool.total_vester - 1;
            let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
            assert!(amount == unobtainable_reward, EAmountNotEnough);
        }
    }

    fun inner_vest_claim(vau: &mut Vault, user_stake: &mut UserVest, ctx: &mut TxContext) {
        let earned = user_stake.earned_reward;
        public_transfer(luck_vault::get_luck(vau, earned, ctx), tx_context::sender(ctx));
        user_stake.earned_reward = 0;
    }


    //hotfix start
    public entry fun deposit_to<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut LuckVault,
        c: vector<NonTransferCoin<ESLUCK>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), EUserNotStake);

        let paid = nonTransferCoin::zero<ESLUCK>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);
        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);


        if (bag::contains(&pool.vester, sender)) {
            let user_vest = bag::borrow_mut<address, UserVest>(&mut pool.vester, sender);
            update_user_vest_earnings(pool.vest_duration, user_vest, clock);
            new_inner_vest_claim(vau, user_vest, ctx);

            //restart when user deposit
            user_vest.amount = user_vest.amount + amount;
            user_vest.unobtainable_reward = 0;
            user_vest.lastet_updated = timestamp_ms(clock);
            user_vest.passed_time = 0;
            nonTransferCoin::join(&mut pool.vest, stake_coin);
        } else {
            bag::add(&mut pool.vester, sender, UserVest {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                lastet_updated: timestamp_ms(clock),
                passed_time: 0,
            });
            nonTransferCoin::join(&mut pool.vest, stake_coin);
            pool.total_vester = pool.total_vester + 1;
        };

        let user_stake = bag::borrow<address, UserStake>(&mut pool.stakes, sender);
        check_deposit_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, user_stake, ctx);
    }

    public entry fun withdraw_to<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut LuckVault,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vester, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vester, sender);
        update_user_vest_earnings(pool.vest_duration, &mut user_vest, clock);
        new_inner_vest_claim(vau, &mut user_vest, ctx);
        let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
        pool.total_vester = pool.total_vester - 1;

        let s_coin = nonTransferCoin::split(&mut pool.vest, sender, amount - unobtainable_reward, ctx);
        public_transfer(s_coin, sender);
    }

    public entry fun claim_vest_luck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut LuckVault,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);

        assert!(bag::contains(&pool.vester, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vester, sender);
        update_user_vest_earnings(pool.vest_duration, &mut user_vest, clock);
        new_inner_vest_claim(vau, &mut user_vest, ctx);
        print(&user_vest);

        if ((user_vest.amount - user_vest.unobtainable_reward) > 0) {
            bag::add(&mut pool.vester, sender, user_vest);
        } else {
            pool.total_vester = pool.total_vester - 1;
            let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
            assert!(amount == unobtainable_reward, EAmountNotEnough);
        }
    }

    fun new_inner_vest_claim(vau: &mut LuckVault, user_stake: &mut UserVest, ctx: &mut TxContext) {
        let earned = user_stake.earned_reward;
        public_transfer(luck_vault::new_get_luck(vau, earned, ctx), tx_context::sender(ctx));
        user_stake.earned_reward = 0;
    }
    //hotfix end


    //hotfix start 9-22
    public entry fun deposit_to_stake<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut RewardLuckVault,
        c: vector<NonTransferCoin<ESLUCK>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), EUserNotStake);

        let paid = nonTransferCoin::zero<ESLUCK>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);
        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);


        if (bag::contains(&pool.vester, sender)) {
            let user_vest = bag::borrow_mut<address, UserVest>(&mut pool.vester, sender);
            update_user_vest_earnings(pool.vest_duration, user_vest, clock);
            reward_inner_vest_claim(vau, user_vest, ctx);

            //restart when user deposit
            user_vest.amount = user_vest.amount + amount;
            user_vest.unobtainable_reward = 0;
            user_vest.lastet_updated = timestamp_ms(clock);
            user_vest.passed_time = 0;
            nonTransferCoin::join(&mut pool.vest, stake_coin);
        } else {
            bag::add(&mut pool.vester, sender, UserVest {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                lastet_updated: timestamp_ms(clock),
                passed_time: 0,
            });
            nonTransferCoin::join(&mut pool.vest, stake_coin);
            pool.total_vester = pool.total_vester + 1;
        };

        let user_stake = bag::borrow<address, UserStake>(&mut pool.stakes, sender);
        check_deposit_amount<REWARD, EXT, LUCK, XLUCK, ESLUCK>(pool, user_stake, ctx);
    }

    public entry fun withdraw_from_stake<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut RewardLuckVault,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vester, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vester, sender);
        update_user_vest_earnings(pool.vest_duration, &mut user_vest, clock);
        reward_inner_vest_claim(vau, &mut user_vest, ctx);
        let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
        pool.total_vester = pool.total_vester - 1;

        let s_coin = nonTransferCoin::split(&mut pool.vest, sender, amount - unobtainable_reward, ctx);
        public_transfer(s_coin, sender);
    }

    public entry fun claim_vest_reward_luck<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        vau: &mut RewardLuckVault,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);

        assert!(bag::contains(&pool.vester, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vester, sender);
        update_user_vest_earnings(pool.vest_duration, &mut user_vest, clock);
        reward_inner_vest_claim(vau, &mut user_vest, ctx);
        print(&user_vest);

        if ((user_vest.amount - user_vest.unobtainable_reward) > 0) {
            bag::add(&mut pool.vester, sender, user_vest);
        } else {
            pool.total_vester = pool.total_vester - 1;
            let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
            assert!(amount == unobtainable_reward, EAmountNotEnough);
        }
    }

    fun reward_inner_vest_claim(vau: &mut RewardLuckVault, user_stake: &mut UserVest, ctx: &mut TxContext) {
        let earned = user_stake.earned_reward;
        public_transfer(luck_vault::get_luck_reward(vau, earned, ctx), tx_context::sender(ctx));
        user_stake.earned_reward = 0;
    }
    //hotfix end

    public fun get_user_vestin<REWARD, EXT, LUCK, XLUCK, ESLUCK>(
        pool: &mut Pool<REWARD, EXT, LUCK, XLUCK, ESLUCK>, ctx: &mut TxContext): (u64, u64) {
        let sender = tx_context::sender(ctx);
        if (bag::contains(&pool.vester, sender)) {
            let user_stake = bag::borrow<address, UserVest>(&pool.vester, sender);
            // amount / time / 1000 * reward_per_sec = how much LUCK stake for reward vetsing amount need
            (user_stake.amount, pool.vest_duration - user_stake.passed_time)
        } else {
            (0, 0)
        }
    }

    fun update_user_vest_earnings(vesting_duration: u64, user_vest: &mut UserVest, clock: &Clock) {
        let now = timestamp_ms(clock);

        let time_diff = now - user_vest.lastet_updated;
        let reward_diff = ((time_diff as u256) * (user_vest.amount as u256) / (vesting_duration as u256) as u64);

        user_vest.earned_reward = user_vest.earned_reward + reward_diff;
        if ((user_vest.unobtainable_reward + reward_diff) > user_vest.amount) {
            user_vest.unobtainable_reward = user_vest.amount;
        } else {
            user_vest.unobtainable_reward = user_vest.unobtainable_reward + reward_diff;
        };

        user_vest.passed_time = user_vest.passed_time + (now - user_vest.lastet_updated);
        user_vest.lastet_updated = now;
    }

    public fun calculate_staker_can_unstake(
        vesting_amount: u64,
        time_left: u64,
        accum_reward: u64,
        user_stake_amount: u64,
        user_unstake_amount: u64
    ) {
        // time_left can not be zero. if this is zero the user can be unstake all the amount
        if (time_left == 0) {
            return
        };
        assert!(user_unstake_amount <= user_stake_amount, EUserCanNotUnStake);
        assert!((((vesting_amount as u256) * (DECIMAL as u256)) >= (accum_reward as u256)),EUserCanNotUnStake);
        let look_amount = ((((vesting_amount as u256) * (DECIMAL as u256)) / (accum_reward as u256)) as u64);

        assert!(look_amount <= user_stake_amount, EUserCanNotUnStake);
        let can_unstake_amount = user_stake_amount - look_amount;

        print(&(11111));
        print(&user_stake_amount);
        print(&user_unstake_amount);
        print(&can_unstake_amount);

        assert!(can_unstake_amount >= user_unstake_amount, EUserCanNotUnStake);
    }

    public fun calculate_staker_need_stake(
        vesting_amount: u64,
        time_left: u64,
        accum_reward: u64,
        user_stake_amount: u64
    ) {
        // time_left can not be zero. if this is zero the user can be unstake all the amount
        if (time_left == 0) {
            return
        };

        // this not need to check, because the user can not unstake all the amount
        // if (vesting_amount >= accum_reward) {
        //     return
        // };

        assert!((((vesting_amount as u256) * (DECIMAL as u256)) >= (accum_reward as u256)),EUserNotHaveEnoughStakeAmount);
        let need_amount = ((((vesting_amount as u256) * (DECIMAL as u256)) / (accum_reward as u256)) as u64);

        print(&need_amount);
        assert!(user_stake_amount >= need_amount, EUserNotHaveEnoughStakeAmount);
    }


    #[test_only]
    const VEST_DURATION: u64 = 1000 * 60 * 60 * 24 * 10; // 10 days


    #[test]
    public fun test_create_stake_pool() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);

        let sui_coin = coin::mint_for_testing<SUI>(15*100000000,&mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
    }

    #[test]
    public fun test_stake() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::{Self, LUCK};
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);

        let r_coin = esLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);

        let sui_coin = coin::mint_for_testing<SUI>(15*100000000,&mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let s_coin = luck::test_mint(&mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LUCK>>();
        vector::push_back(&mut s, s_coin);
        staking::stake_luck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        // let s_coin = xLuck::
        // let coin_val = coin::value(&s_coin);
        // let s = vector::empty<Coin<XLUCK>>();
        // vector::push_back(&mut s, s_coin);
        // staking::stake_xluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }


    #[test]
    public fun test_claim() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::{Self, LUCK};
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);

        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000 / 2,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let s_coin = luck::test_mint(&mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LUCK>>();
        vector::push_back(&mut s, s_coin);
        staking::stake_luck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);
        next_tx(&mut scenario, sender);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);

        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == 600 * 1000000000, 1);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        test_scenario::return_to_sender(&scenario, ntc);
        end(scenario);
    }

    #[test]
    public fun test_unstake_luck() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::{Self, LUCK};
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);

        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);


        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let s_coin = luck::test_mint(&mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LUCK>>();
        vector::push_back(&mut s, s_coin);
        staking::stake_luck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 86400 * 1000000000, 1);
        test_scenario::return_to_sender(&scenario, ntc);

        staking::unstake_luck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, 15 * 100000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<Coin<LUCK>>(&scenario);
        assert!(coin::value(&s) == (15 * 100000000), 1);
        test_scenario::return_to_sender(&mut scenario, s);


        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    public fun test_unstake_xluck() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let mintable = xLuck::test_init(&mut ctx);
        let s_coin = xLuck::test_mint(&mut mintable, 15 * 100000000, &mut ctx);


        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<XLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_xluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 86400 * 1000000000, 1);
        test_scenario::return_to_sender(&scenario, ntc);

        staking::unstake_xluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, 15 * 100000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<NonTransferCoin<XLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&s) == (15 * 100000000), 1);
        test_scenario::return_to_sender(&mut scenario, s);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    public fun test_unstake_esluck() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, 15 * 100000000, &mut ctx);

        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        // clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        // staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        //
        // next_tx(&mut scenario, sender);
        // let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        // assert!(nonTransferCoin::value(&ntc) == 86400000 * 1000000000, 1);
        // test_utils::destroy(ntc);
        next_tx(&mut scenario, sender);
        staking::unstake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, 15 * 100000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);

        //FIX there some bugs in take from sender. assert!(nonTransferCoin::value(&s) == (15 * 100000000), 1);

        test_scenario::return_to_sender(&mut scenario, s);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    public fun test_unstake_esluck_times() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, 15 * 100000000, &mut ctx);

        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1002 * 60 * 60 * 24);

        staking::unstake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, 15 * 100000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);

        //FIX there some bugs in take from sender. assert!(nonTransferCoin::value(&s) == (15 * 100000000), 1);

        test_scenario::return_to_sender(&mut scenario, s);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test_only]
    fun init_vault(scenario: &mut Scenario, ctx: &mut TxContext): Vault {
        luck_vault::init_vault(ctx);
        next_tx(scenario, tx_context::sender(ctx));
        let v = test_scenario::take_shared<Vault>(scenario);
        let coin = coin::mint_for_testing<LUCK>(1000000000 * 1000000000, ctx);
        luck_vault::deposit_luck(&mut v, coin, ctx);
        v
    }

    #[test]
    fun test_vesting() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        //let default_vester_amout:u64 = 1000000000;


        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);
        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, 15 * 1000000000, &mut ctx);

        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 2);
        next_tx(&mut scenario, sender);

        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);

        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 2 * 1000000000, 1);

        let amount = nonTransferCoin::value(&ntc);

        next_tx(&mut scenario, sender);

        let valut = init_vault(&mut scenario, &mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, ntc);
        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, amount, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 100);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        //staking::unstake_esluck(&mut pool, 10 * 1000000000, &clock, &mut ctx);

        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        let amount = nonTransferCoin::value(&ntc) - 1000000000 * 5000000;
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, ntc);
        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, amount, &clock, &mut ctx);
        next_tx(&mut scenario, sender);

        let ntc = esLuck::test_mint(&mut mintable, 1000000000 * 5000000, &mut ctx);
        let amount = nonTransferCoin::value(&ntc);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, ntc);
        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, amount, &clock, &mut ctx);


        test_scenario::return_shared(valut);
        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    fun test_put_less_amount_for_vest() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);
        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, 15 * 1000000000, &mut ctx);

        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 2);
        next_tx(&mut scenario, sender);

        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 2 * 1000000000, 1);
        let amount = nonTransferCoin::value(&ntc);
        next_tx(&mut scenario, sender);

        let valut = init_vault(&mut scenario, &mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, ntc);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 100);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);

        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 100 * 1000000000, 1);
        next_tx(&mut scenario, sender);
        test_utils::destroy(ntc);

        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, amount, &clock, &mut ctx);

        test_scenario::return_shared(valut);
        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    #[expected_failure(abort_code = EUserNotHaveEnoughStakeAmount)]
    fun test_put_max_amount_for_vest() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);
        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, 15 * 1000000000, &mut ctx);

        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 2);
        next_tx(&mut scenario, sender);

        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 2 * 1000000000, 1);
        let amount = nonTransferCoin::value(&ntc);
        next_tx(&mut scenario, sender);

        let valut = init_vault(&mut scenario, &mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, ntc);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 100);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);

        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 100 * 1000000000, 1);
        next_tx(&mut scenario, sender);
        //test_utils::destroy(ntc);
        let amount = amount + nonTransferCoin::value(&ntc);
        vector::push_back(&mut s, ntc);
        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, amount, &clock, &mut ctx);

        //this is ok for now. but we cannot put more in here. if you want you need stake more XLUCK.
        let n = esLuck::test_mint(&mut mintable, 1*100000000, &mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, n);
        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, 1*100000000, &clock, &mut ctx);


        test_scenario::return_shared(valut);
        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }


    #[test]
    #[expected_failure(abort_code = EUserCanNotUnStake)]
    fun test_cannot_unstake_when_have_vest() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::LUCK;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        test_utils::destroy(mintable);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);
        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, 15 * 1000000000, &mut ctx);

        let coin_val = nonTransferCoin::value(&s_coin);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);

        staking::stake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 2);
        next_tx(&mut scenario, sender);

        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 2 * 1000000000, 1);
        let amount = nonTransferCoin::value(&ntc);
        next_tx(&mut scenario, sender);

        let valut = init_vault(&mut scenario, &mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, ntc);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24 * 100);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);

        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 100 * 1000000000, 1);
        next_tx(&mut scenario, sender);
        test_utils::destroy(ntc);
        deposit<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &mut valut, s, amount, &clock, &mut ctx);
        staking::unstake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool,12 * 1000000000, &clock, &mut ctx);
        //this will fail
        staking::unstake_esluck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool,3 * 1000000000, &clock, &mut ctx);

        test_scenario::return_shared(valut);
        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }


    #[test]
    public fun test_single_staker() {
        use sui::tx_context;
        use staking::staking;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use luck::luck::{Self, LUCK};
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);

        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);

        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        staking::create_stake_pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000 / 2,
            1000000000,
            VEST_DURATION,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>>(&mut scenario);

        let s_coin = luck::test_mint(&mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LUCK>>();
        vector::push_back(&mut s, s_coin);
        staking::stake_luck<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        next_tx(&mut scenario, sender);
        staking::claim<ESLUCK, SUI, LUCK, XLUCK, ESLUCK>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);

        assert!(nonTransferCoin::value(&ntc) == 60 * 60 * 24 * 1000000000, 1);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        test_scenario::return_to_sender(&scenario, ntc);
        end(scenario);
    }
}
