module staking::stake_lp {
    use std::debug::print;

    use admin::admin::{is_admin, Manage};
    use token::nonTransferCoin::{Self, NonTransferCoin};
    use utils::utils;

    use sui::bag::{Self, Bag};
    use sui::clock::{timestamp_ms, Clock};
    use sui::coin::{Self, Coin};
    use sui::object::{Self, UID};
    use sui::pay;
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::{Self, TxContext};

    #[test_only]
    use staking::stake_lp;
    #[test_only]
    use std::vector;
    #[test_only]
    use sui::test_scenario::next_tx;
    #[test_only]
    use sui::test_utils;
    #[test_only]
    use llp::llp::LLP;
    #[test_only]
    use sui::sui::{SUI};


    const VERSION: u64 = 1;
    const EWrongVersion: u64 = 2001;

    const ETimestampElapsed: u64 = 1002;
    const ENoStake: u64 = 1003;
    const EPoolEmergencyLocked: u64 = 1004;
    const ERequireAdminPermission: u64 = 1005;
    const EStakeValue: u64 = 1006;


    struct Pool<phantom REWARD, phantom EXT, phantom LP> has key, store {
        id: UID,
        lp_coin: Coin<LP>,

        esluck_reward_coin: NonTransferCoin<REWARD>,
        ext_reward_coin: Coin<EXT>,

        reward_per_sec: u64,
        ext_reward_per_sec: u64,

        accum_reward:  u64,
        ext_accum_reward: u64,

        start_timestamp: u64,
        end_timestamp: u64,
        last_updated: u64,

        scale: u64,

        stakes: Bag,
        emergency_locked: bool,

        total_stakers: u256,
        total_rewards: u256,
        version: u64,
    }

    /// Stores user stake info.
    struct UserStake has store, drop {
        amount: u64,
        unobtainable_reward: u64,
        earned_reward: u64,
        earned_per_token_store:u64,

        ext_earned_reward: u64,
        ext_unobtainable_reward: u64,
        ext_earned_per_token_store:u64,
    }

    public entry fun add_reward_coin<REWARD, EXT, LP>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LP>,
        reward_coins: NonTransferCoin<REWARD>,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        assert!(pool.version == VERSION, EWrongVersion);

        nonTransferCoin::join(&mut pool.esluck_reward_coin, reward_coins)
    }

    public entry fun add_ext_reward_coin<REWARD, EXT, LP>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LP>,
        sui_coin: Coin<EXT>,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        assert!(pool.version == VERSION, EWrongVersion);

        coin::join(&mut pool.ext_reward_coin, sui_coin)
    }

    public entry fun change_reward_per_sec<REWARD, EXT, LP>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LP>,
        reward_per_sec: u64,
        scale: u64,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        assert!(pool.version == VERSION, EWrongVersion);

        pool.scale = scale;
        pool.reward_per_sec = reward_per_sec;
    }

    public entry fun change_ext_reward_per_sec<REWARD, EXT, LP>(
        adm: &mut Manage,
        pool: &mut Pool<REWARD, EXT, LP>,
        ext_reward_per_sec: u64,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        pool.ext_reward_per_sec = ext_reward_per_sec;
    }

    public entry fun create_stake_pool<REWARD, EXT, LP>(
        adm: &mut Manage,
        reward_coins: NonTransferCoin<REWARD>,
        ext_reward_coin: Coin<EXT>,
        reward_per_sec: u64,
        ext_reward_per_sec: u64,
        scale: u64,
        end_timestamp: u64,
        lock: &Clock,
        ctx: &mut TxContext,
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        let start_timestamp = timestamp_ms(lock);
        assert!(end_timestamp > start_timestamp, ETimestampElapsed);
        
        public_share_object(Pool<REWARD, EXT, LP> {
            id: object::new(ctx),
            lp_coin: coin::zero(ctx),
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
            total_stakers: 0,
            total_rewards: 0,
            version: VERSION,
        });
    }

    fun get_time_for_last_update<REWARD, EXT, LP>(
        pool: &Pool<REWARD, EXT, LP>,
        clock: &Clock
    ): u64 {
        if (pool.end_timestamp < timestamp_ms(clock)) {
            pool.end_timestamp
        } else {
            timestamp_ms(clock)
        }
    }

    fun update_accum_reward<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
        clock: &Clock
    ) {
        let current_time = get_time_for_last_update(pool, clock);
        let (new_accum_rewards, new_ext_accum_rewards) = accum_rewards_since_last_updated(pool, current_time);


        pool.last_updated = current_time;
        if (new_accum_rewards != 0) {
            pool.accum_reward = pool.accum_reward + new_accum_rewards;
        };

        if (new_ext_accum_rewards != 0) {
            pool.ext_accum_reward = pool.ext_accum_reward + new_ext_accum_rewards;
        }
    }


    fun accum_rewards_since_last_updated<REWARD, EXT, LP>(
        pool: &Pool<REWARD, EXT, LP>,
        current_time: u64
    ): (u64, u64) {

        let time_diff = (current_time - pool.last_updated) / 1000;
        let total_supply = coin::value(&pool.lp_coin);

        if (total_supply == 0) {
            (0,0)
        } else {
            //(math::divide_and_round_up(time_diff * pool.reward_per_sec * pool.scale,total_supply),math::divide_and_round_up(time_diff * pool.ext_reward_per_sec  * pool.scale,total_supply))
            let reward_per_token = ((time_diff as u256) * (pool.reward_per_sec as u256) * (pool.scale as u256) / (total_supply as u256) as u64);
            let ext_reward_per_token = ((time_diff as u256) * (pool.ext_reward_per_sec as u256) * (pool.scale as u256) / (total_supply as u256) as u64);
            (reward_per_token,ext_reward_per_token)
        }
    }

    fun update_user_earnings(
        accum_reward: u64,
        ext_accum_reward: u64,
        scale: u64,
        user_stake: &mut UserStake
    ) {
        let earned =
            user_earned_since_last_update(accum_reward, scale, user_stake);

        user_stake.earned_reward = user_stake.earned_reward + earned;
        user_stake.unobtainable_reward = user_stake.unobtainable_reward + earned;
        user_stake.earned_per_token_store = accum_reward;

        let ext_earned = ext_user_earned_since_last_update(ext_accum_reward, scale, user_stake);

        user_stake.ext_earned_reward = user_stake.ext_earned_reward + ext_earned;
        user_stake.ext_unobtainable_reward = user_stake.ext_unobtainable_reward + ext_earned;
        user_stake.ext_earned_per_token_store = ext_accum_reward;
    }

    fun user_earned_since_last_update(
        accum_reward: u64,
        scale: u64,
        user_stake: &UserStake
    ): u64 {
        (((user_stake.amount as u256) * ((accum_reward - user_stake.earned_per_token_store) as u256) / (scale as u256)) as u64)
    }

    fun ext_user_earned_since_last_update(
        accum_reward: u64,
        scale: u64,
        user_stake: &UserStake
    ): u64 {
        (((user_stake.amount as u256) * ((accum_reward - user_stake.ext_earned_per_token_store) as u256) / (scale as u256)) as u64)
    }

    public entry fun stake<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
        c: vector<Coin<LP>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(pool.version == VERSION, EWrongVersion);
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let paid = coin::zero<LP>(ctx);
        pay::join_vec(&mut paid, c);
        assert!(coin::value(&paid) >= amount, 1001);
        let sender = tx_context::sender(ctx);
        let stake_coin = coin::split(&mut paid, amount, ctx);
        utils::destroy_zero_or_transfer(paid, ctx);
        update_accum_reward(pool, clock);

        if (bag::contains(&pool.stakes, sender)) {
            let user_stake = bag::remove<address, UserStake>(&mut pool.stakes, sender);

            update_user_earnings(
                pool.accum_reward,
                pool.ext_accum_reward,
                pool.scale,
                &mut user_stake
            );

            inner_claim(pool, &mut user_stake, ctx);

            user_stake.amount = user_stake.amount + amount;
            bag::add(&mut pool.stakes, sender, user_stake);
            coin::join(&mut pool.lp_coin, stake_coin);
        } else {
            coin::join(&mut pool.lp_coin, stake_coin);
            bag::add(&mut pool.stakes, sender, UserStake {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                ext_earned_reward: 0,
                ext_unobtainable_reward: 0,
                earned_per_token_store: pool.accum_reward,
                ext_earned_per_token_store:pool.ext_accum_reward
            });
            pool.total_stakers = pool.total_stakers + 1;
        }
    }


    public fun get_user_total_stake<REWARD, EXT, LP>(
        pool: &Pool<REWARD, EXT, LP>,
        ctx: &mut TxContext
    ): u64 {
        let sender = tx_context::sender(ctx);
        let user_stake = bag::borrow<address, UserStake>(&pool.stakes, sender);
        user_stake.amount
    }


    public entry fun unstake<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(pool.version == VERSION, EWrongVersion);
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), ENoStake);
        update_accum_reward(pool, clock);
        let user_stake = bag::remove<address, UserStake>(&mut pool.stakes, sender);
        update_user_earnings(
            pool.accum_reward,
            pool.ext_accum_reward,
            pool.scale,
            &mut user_stake
        );

        assert!(user_stake.amount >= amount, EStakeValue);
        inner_claim(pool, &mut user_stake, ctx);
        user_stake.amount = user_stake.amount - amount;

        let luck = coin::split(&mut pool.lp_coin, amount, ctx);
        public_transfer(luck, sender);

        if (user_stake.amount == 0) {
            safe_remove_user_stake(pool, user_stake);
        } else {
            bag::add(&mut pool.stakes, sender, user_stake);
        }
    }

    public entry fun claim<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(pool.version == VERSION, EWrongVersion);
        assert!(!pool.emergency_locked, EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.stakes, sender), ENoStake);
        update_accum_reward(pool, clock);

        let user_stake = bag::remove(&mut pool.stakes, sender);

        update_user_earnings(
            pool.accum_reward,
            pool.ext_accum_reward,
            pool.scale,
            &mut user_stake
        );

        inner_claim(pool, &mut user_stake, ctx);
        bag::add(&mut pool.stakes, sender, user_stake);
    }

    fun inner_claim<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
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
        print(&123);
        print(&user_stake.ext_earned_reward);
        public_transfer(ext_r_coin, sender);

        user_stake.earned_reward = 0;
        user_stake.ext_earned_reward = 0;
    }

    fun safe_remove_user_stake<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
        user_stake: UserStake
    ) {
        assert!(user_stake.amount == 0, EStakeValue);
        assert!(user_stake.earned_reward == 0, EStakeValue);
        assert!(user_stake.ext_earned_reward == 0, EStakeValue);

        pool.total_stakers = pool.total_stakers - 1;
    }

    public entry fun enable_emergency<REWARD, EXT, LP>(
        pool: &mut Pool<REWARD, EXT, LP>,
        adm: &mut Manage,
        ctx: &mut TxContext
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        assert!(pool.version == VERSION, EWrongVersion);

        pool.emergency_locked = true;
    }

    #[test]
    public fun test_create_stake_pool() {
        use sui::tx_context;
        use admin::admin;
        use esluck::esLuck;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);
        let r_coin = esLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        let sui_coin = coin::mint_for_testing<SUI>(15*100000000,&mut ctx);
        create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            1000000000,
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
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;

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
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            1000000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }


    #[test]
    public fun test_claim() {
        use sui::tx_context;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
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
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(60000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        next_tx(&mut scenario, sender);
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == 86400 * 1000000000, 1);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        test_scenario::return_to_sender(&scenario, ntc);
        end(scenario);
    }

    #[test]
    public fun test_unstaking() {
        use sui::tx_context;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
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
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 86400 * 1000000000, 1);
        test_scenario::return_to_sender(&scenario, ntc);

        stake_lp::unstake<ESLUCK, SUI, LLP>(&mut pool, 1000000000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<Coin<LLP>>(&scenario);
        assert!(coin::value(&s) == 1000000000000, 1);
        test_scenario::return_to_sender(&mut scenario, s);

        stake_lp::unstake<ESLUCK, SUI, LLP>(&mut pool, 1000000000000000 - 1000000000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<Coin<LLP>>(&scenario);
        assert!(coin::value(&s) == (1000000000000000 - 1000000000000), 1);
        test_scenario::return_to_sender(&mut scenario, s);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    #[expected_failure]
    public fun test_unstaking_failed() {
        use sui::tx_context;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
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
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1,
            1,
            100000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 60 * 24);
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        assert!(nonTransferCoin::value(&ntc) == 86400 * 1000000000, 1);
        test_scenario::return_to_sender(&scenario, ntc);

        stake_lp::unstake<ESLUCK, SUI, LLP>(&mut pool, 1000000000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<Coin<LLP>>(&scenario);
        assert!(coin::value(&s) == 1000000000000, 1);
        test_scenario::return_to_sender(&mut scenario, s);

        stake_lp::unstake<ESLUCK, SUI, LLP>(&mut pool, 1000000000000000 - 1000000000000, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let s = test_scenario::take_from_sender<Coin<LLP>>(&scenario);
        assert!(coin::value(&s) == (1000000000000001 - 1000000000000), 1);
        test_scenario::return_to_sender(&mut scenario, s);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    //entry fun m
    // entry fun migrate(p: &mut Pool, a: &AdminCap) {
    //     assert!(c.admin == object::id(a), ENotAdmin);
    //     assert!(c.version < VERSION, ENotUpgrade);
    //     c.version = VERSION;
    // }

    #[test]
    public fun test_single_staker() {
        use sui::tx_context;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
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
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000,
            500000,
            1000000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(100000 * 1000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        clock::set_for_testing(&mut clock, 0);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);
        next_tx(&mut scenario, sender);
        let s_coin = coin::mint_for_testing<LLP>(1000000 * 1000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600 * 1000000), 1);
        test_utils::destroy(ntc);

        let sui = test_scenario::take_from_sender<Coin<SUI>>(&scenario);
        print(&sui);
        assert!(coin::value(&sui) == (600 * 1000000 / 2), 1);
        test_utils::destroy(sui);

        next_tx(&mut scenario, sender);

        clock::increment_for_testing(&mut clock, 1000 * 60* 10);
        next_tx(&mut scenario, sender);
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == 599500000, 1);
        test_utils::destroy(ntc);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);
        next_tx(&mut scenario, sender);
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == 599500000, 1);
        test_utils::destroy(ntc);

        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
    }


    #[test]
    public fun test_many_staker() {
        use sui::tx_context;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));
        let scenario_1 = test_scenario::begin(@0xB0B);

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);

        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);


        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000000,
            1000000000,
            1000000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(100000 * 1000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == 600 * 1000000000, 1);
        test_utils::destroy(ntc);
        next_tx(&mut scenario, sender);


        // stake B started
        let s_coin = coin::mint_for_testing<LLP>(100000 * 1000000000, test_scenario::ctx(&mut scenario_1));
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, test_scenario::ctx(&mut scenario_1));
        next_tx(&mut scenario, sender);

        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);


        // check B
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, test_scenario::ctx(&mut scenario_1));
        next_tx(&mut scenario_1, @0xB0B);
        let ntc = test_scenario::take_from_address<NonTransferCoin<ESLUCK>>(&scenario_1, @0xB0B);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000000 / 2), 1);
        test_utils::destroy(ntc);


        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);

        next_tx(&mut scenario, sender);
        // stake a check
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000000), 1);
        test_utils::destroy(ntc);

        // check B
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, test_scenario::ctx(&mut scenario_1));
        next_tx(&mut scenario_1, @0xB0B);
        let ntc = test_scenario::take_from_address<NonTransferCoin<ESLUCK>>(&scenario_1, @0xB0B);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000000 / 2), 1);
        test_utils::destroy(ntc);


        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
        end(scenario_1);
    }



    #[test]
    public fun test_many_staker_1() {
        use sui::tx_context;
        use admin::admin;
        use sui::test_scenario::{Self, end};
        use esluck::esLuck;
        use esluck::esLuck::{ESLUCK};
        use sui::clock;
        use sui::test_utils::destroy;

        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);

        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));
        let scenario_1 = test_scenario::begin(@0xB0B);

        let adm = admin::test_init(&mut ctx);
        let mintable = esLuck::test_init(&mut ctx);

        let r_coin = esLuck::test_mint(&mut mintable, 1000000000000000000, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);


        let sui_coin = coin::mint_for_testing(1000000000000000000, &mut ctx);
        stake_lp::create_stake_pool<ESLUCK, SUI, LLP>(
            &mut adm,
            r_coin,
            sui_coin,
            1000000,
            500000,
            1000000000,
            17134948850000,
            &clock,
            &mut ctx
        );

        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK, SUI, LLP>>(&mut scenario);

        let s_coin = coin::mint_for_testing<LLP>(100000 * 1000000000, &mut ctx);
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, &mut ctx);

        // stake B started
        let s_coin = coin::mint_for_testing<LLP>(100000 * 1000000000, test_scenario::ctx(&mut scenario_1));
        let coin_val = coin::value(&s_coin);
        let s = vector::empty<Coin<LLP>>();
        vector::push_back(&mut s, s_coin);
        stake_lp::stake<ESLUCK, SUI, LLP>(&mut pool, s, coin_val, &clock, test_scenario::ctx(&mut scenario_1));
        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);


        // stake a check
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000 / 2), 1);
        test_utils::destroy(ntc);

        // check B
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, test_scenario::ctx(&mut scenario_1));
        next_tx(&mut scenario_1, @0xB0B);
        let ntc = test_scenario::take_from_address<NonTransferCoin<ESLUCK>>(&scenario_1, @0xB0B);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000 / 2), 1);
        test_utils::destroy(ntc);


        next_tx(&mut scenario, sender);
        clock::increment_for_testing(&mut clock, 1000 * 60 * 10);

        next_tx(&mut scenario, sender);
        // stake a check
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let ntc = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&scenario);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000 / 2), 1);
        test_utils::destroy(ntc);

        // check B
        stake_lp::claim<ESLUCK, SUI, LLP>(&mut pool, &clock, test_scenario::ctx(&mut scenario_1));
        next_tx(&mut scenario_1, @0xB0B);
        let ntc = test_scenario::take_from_address<NonTransferCoin<ESLUCK>>(&scenario_1, @0xB0B);
        print(&ntc);
        assert!(nonTransferCoin::value(&ntc) == (600* 1000000 / 2), 1);
        test_utils::destroy(ntc);


        admin::test_delete(adm);
        destroy(mintable);
        destroy(clock);
        test_scenario::return_shared(pool);
        end(scenario);
        end(scenario_1);
    }
}
