module staking::vesting {
    use admin::admin::{is_admin, Manage};
    use token::nonTransferCoin::{Self, NonTransferCoin};
    use staking::luck_vault::{Self, Vault, LuckVault, RewardLuckVault};
    use sui::clock::{timestamp_ms, Clock};
    use sui::object::{Self, UID};
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::{Self, TxContext};
    use sui::bag::Bag;
    use sui::bag;


    #[test_only]
    use admin::admin;
    #[test_only]
    use luck::luck::LUCK;
    #[test_only]
    use std::vector;
    #[test_only]
    use sui::clock;
    #[test_only]
    use sui::coin;
    #[test_only]
    use sui::test_scenario::{Self, end, next_tx,Scenario};
    #[test_only]
    use sui::test_utils;
    #[test_only]
    use esluck::esLuck::{Self, ESLUCK};
    #[test_only]
    use sui::coin::Coin;
    #[test_only]
    use std::debug::print;


    struct Pool<phantom S> has key, store {
        id: UID,
        stake_coins: NonTransferCoin<S>,
        vesting_duration: u64,
        vesters: Bag,
        emergency_locked: bool,
        total_vested: u256,
        total_vesters: u256,
        total_vester_rewards: u256,
    }


    const EAmountNotEnough: u64 = 1002;
    const ENoStake: u64 = 1003;
    const EPoolEmergencyLocked: u64 = 1004;
    const ERequireAdminPermission: u64 = 1005;

    /// Stores user stake info.
    struct UserVest has store {
        amount: u64,
        unobtainable_reward: u64,
        earned_reward: u64,
        lastet_updated: u64,
        passed_time: u64,
    }

    public entry fun create_pool<S>(
        adm: &mut Manage,
        duration: u64,
        ctx: &mut TxContext,
    ) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);

        public_share_object(Pool {
            id: object::new(ctx),
            stake_coins: nonTransferCoin::zero<S>(tx_context::sender(ctx), ctx),
            vesting_duration: duration,
            vesters: bag::new(ctx),
            emergency_locked: false,
            total_vested: 0,
            total_vesters: 0,
            total_vester_rewards: 0,
        });
    }

    public entry fun deposit<S>(
        pool: &mut Pool<S>,
        vau: &mut Vault,
        //stake_pool:&StakePool<REWARD, EXT, LUCK, XLUCK, ESLUCK>,
        c: vector<NonTransferCoin<S>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);

        let sender = tx_context::sender(ctx);
        let paid = nonTransferCoin::zero<S>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);
        nonTransferCoin::join(&mut pool.stake_coins, stake_coin);
        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);

        if (bag::contains(&pool.vesters, sender)) {
            let user_vest = bag::borrow_mut<address, UserVest>(&mut pool.vesters, sender);
            update_user_earnings(pool.vesting_duration, user_vest, clock);
            inner_claim(vau, user_vest, ctx);

            //restart when user deposit
            user_vest.amount = user_vest.amount + amount;
            user_vest.unobtainable_reward = 0;
            user_vest.lastet_updated = timestamp_ms(clock);
            user_vest.passed_time = 0;
            pool.total_vested = pool.total_vested  + (amount as u256);
        } else {
            bag::add(&mut pool.vesters, sender, UserVest {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                lastet_updated: timestamp_ms(clock),
                passed_time: 0,
            });

            pool.total_vested = pool.total_vested  + (amount as u256);
            pool.total_vesters = pool.total_vesters + 1;
        }
    }

    public entry fun withdraw<S>(pool: &mut Pool<S>, vau: &mut Vault, clock: &Clock, ctx: &mut TxContext) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vesters, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vesters, sender);
        update_user_earnings(pool.vesting_duration, &mut user_vest, clock);
        inner_claim(vau, &mut user_vest, ctx);
        let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
        pool.total_vesters = pool.total_vesters - 1;
        pool.total_vested = pool.total_vested  - ((amount - unobtainable_reward) as u256);

        let s_coin = nonTransferCoin::split(&mut pool.stake_coins, sender, amount - unobtainable_reward, ctx);
        public_transfer(s_coin, sender);
    }

    public entry fun claim<S>(pool: &mut Pool<S>, vau: &mut Vault, clock: &Clock, ctx: &mut TxContext) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vesters, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vesters, sender);
        update_user_earnings(pool.vesting_duration, &mut user_vest, clock);
        inner_claim(vau, &mut user_vest, ctx);

        if (user_vest.amount != user_vest.unobtainable_reward) {
            bag::add(&mut pool.vesters, sender, user_vest);
        } else {
            pool.total_vesters = pool.total_vesters - 1;
            let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
            assert!(amount == unobtainable_reward, EAmountNotEnough);
        }
    }

    fun inner_claim(vau: &mut Vault, user_stake: &mut UserVest, ctx: &mut TxContext) {
        let earned = user_stake.earned_reward;
        public_transfer(luck_vault::get_luck(vau, earned, ctx), tx_context::sender(ctx));
        user_stake.earned_reward = 0;
    }



    // hotfix start
    public entry fun deposit_to<S>(
        pool: &mut Pool<S>,
        vau: &mut LuckVault,
        c: vector<NonTransferCoin<S>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);

        let sender = tx_context::sender(ctx);
        let paid = nonTransferCoin::zero<S>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);
        nonTransferCoin::join(&mut pool.stake_coins, stake_coin);
        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);

        if (bag::contains(&pool.vesters, sender)) {
            let user_vest = bag::borrow_mut<address, UserVest>(&mut pool.vesters, sender);
            update_user_earnings(pool.vesting_duration, user_vest, clock);
            new_inner_claim(vau, user_vest, ctx);

            //restart when user deposit
            user_vest.amount = user_vest.amount + amount;
            user_vest.unobtainable_reward = 0;
            user_vest.lastet_updated = timestamp_ms(clock);
            user_vest.passed_time = 0;
            pool.total_vested = pool.total_vested  + (amount as u256);
        } else {
            bag::add(&mut pool.vesters, sender, UserVest {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                lastet_updated: timestamp_ms(clock),
                passed_time: 0,
            });

            pool.total_vested = pool.total_vested  + (amount as u256);
            pool.total_vesters = pool.total_vesters + 1;
        }
    }

    public entry fun withdraw_to<S>(pool: &mut Pool<S>, vau: &mut LuckVault, clock: &Clock, ctx: &mut TxContext) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vesters, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vesters, sender);
        update_user_earnings(pool.vesting_duration, &mut user_vest, clock);
        new_inner_claim(vau, &mut user_vest, ctx);
        let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
        pool.total_vesters = pool.total_vesters - 1;
        pool.total_vested = pool.total_vested  - ((amount - unobtainable_reward) as u256);

        let s_coin = nonTransferCoin::split(&mut pool.stake_coins, sender, amount - unobtainable_reward, ctx);
        public_transfer(s_coin, sender);
    }


    public entry fun claim_luck<S>(pool: &mut Pool<S>, vau: &mut LuckVault, clock: &Clock, ctx: &mut TxContext) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vesters, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vesters, sender);
        update_user_earnings(pool.vesting_duration, &mut user_vest, clock);
        new_inner_claim(vau, &mut user_vest, ctx);

        if (user_vest.amount != user_vest.unobtainable_reward) {
            bag::add(&mut pool.vesters, sender, user_vest);
        } else {
            pool.total_vesters = pool.total_vesters - 1;
            let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
            assert!(amount == unobtainable_reward, EAmountNotEnough);
        }
    }


    fun new_inner_claim(vau: &mut LuckVault, user_stake: &mut UserVest, ctx: &mut TxContext) {
        let earned = user_stake.earned_reward;
        public_transfer(luck_vault::new_get_luck(vau, earned, ctx), tx_context::sender(ctx));
        user_stake.earned_reward = 0;
    }
    //hotfix end


    // hotfix start 9-22
    public entry fun deposit_to_vesting<S>(
        pool: &mut Pool<S>,
        vau: &mut RewardLuckVault,
        c: vector<NonTransferCoin<S>>,
        amount: u64,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);

        let sender = tx_context::sender(ctx);
        let paid = nonTransferCoin::zero<S>(sender, ctx);
        nonTransferCoin::join_vec(&mut paid, c);
        assert!(nonTransferCoin::value(&paid) >= amount, 1001);
        let stake_coin = nonTransferCoin::split(&mut paid, sender, amount, ctx);
        nonTransferCoin::join(&mut pool.stake_coins, stake_coin);
        nonTransferCoin::destroy_zero_or_transfer(paid, ctx);

        if (bag::contains(&pool.vesters, sender)) {
            let user_vest = bag::borrow_mut<address, UserVest>(&mut pool.vesters, sender);
            update_user_earnings(pool.vesting_duration, user_vest, clock);
            reward_inner_claim(vau, user_vest, ctx);

            //restart when user deposit
            user_vest.amount = user_vest.amount + amount;
            user_vest.unobtainable_reward = 0;
            user_vest.lastet_updated = timestamp_ms(clock);
            user_vest.passed_time = 0;
            pool.total_vested = pool.total_vested  + (amount as u256);
        } else {
            bag::add(&mut pool.vesters, sender, UserVest {
                amount,
                unobtainable_reward: 0,
                earned_reward: 0,
                lastet_updated: timestamp_ms(clock),
                passed_time: 0,
            });

            pool.total_vested = pool.total_vested  + (amount as u256);
            pool.total_vesters = pool.total_vesters + 1;
        }
    }

    public entry fun withdraw_from_vesting<S>(pool: &mut Pool<S>, vau: &mut RewardLuckVault, clock: &Clock, ctx: &mut TxContext) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vesters, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vesters, sender);
        update_user_earnings(pool.vesting_duration, &mut user_vest, clock);
        reward_inner_claim(vau, &mut user_vest, ctx);
        let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
        pool.total_vesters = pool.total_vesters - 1;
        pool.total_vested = pool.total_vested  - ((amount - unobtainable_reward) as u256);

        let s_coin = nonTransferCoin::split(&mut pool.stake_coins, sender, amount - unobtainable_reward, ctx);
        public_transfer(s_coin, sender);
    }


    public entry fun claim_luck_reward<S>(pool: &mut Pool<S>, vau: &mut RewardLuckVault, clock: &Clock, ctx: &mut TxContext) {
        assert!(!pool.emergency_locked,  EPoolEmergencyLocked);
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&pool.vesters, sender), ENoStake);

        let user_vest = bag::remove(&mut pool.vesters, sender);
        update_user_earnings(pool.vesting_duration, &mut user_vest, clock);
        reward_inner_claim(vau, &mut user_vest, ctx);

        if (user_vest.amount != user_vest.unobtainable_reward) {
            bag::add(&mut pool.vesters, sender, user_vest);
        } else {
            pool.total_vesters = pool.total_vesters - 1;
            let UserVest { amount, unobtainable_reward, earned_reward: _, lastet_updated: _, passed_time: _ } = user_vest;
            assert!(amount == unobtainable_reward, EAmountNotEnough);
        }
    }


    fun reward_inner_claim(vau: &mut RewardLuckVault, user_stake: &mut UserVest, ctx: &mut TxContext) {
        let earned = user_stake.earned_reward;
        public_transfer(luck_vault::get_luck_reward(vau, earned, ctx), tx_context::sender(ctx));
        user_stake.earned_reward = 0;
    }
    //hotfix end

    public entry fun get_user_vesting<S>(pool: &Pool<S>, ctx: &mut TxContext): (u64, u64) {
        let sender = tx_context::sender(ctx);
        if (bag::contains(&pool.vesters, sender)) {
            let user_stake = bag::borrow<address,UserVest>(&pool.vesters, sender);
            // amount / time / 1000 * reward_per_sec = how much LUCK stake for reward vetsing amount need
            (user_stake.amount, pool.vesting_duration - user_stake.passed_time)
        } else {
            (0, 0)
        }
    }

    public entry fun enable_emergency<S>(pool: &mut Pool<S>, adm: &mut Manage, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        pool.emergency_locked = true;
    }

    fun update_user_earnings(vesting_duration: u64, user_vest: &mut UserVest, clock: &Clock) {
        let now = timestamp_ms(clock);

        let time_diff = now - user_vest.lastet_updated;
        let reward_diff = ((time_diff as u256) * (user_vest.amount as u256) / (vesting_duration as u256) as u64);



        if ((user_vest.unobtainable_reward + reward_diff) > user_vest.amount) {
            user_vest.earned_reward = user_vest.amount;
            user_vest.unobtainable_reward = user_vest.amount;
        } else {
            user_vest.earned_reward = user_vest.earned_reward + reward_diff;
            user_vest.unobtainable_reward = user_vest.unobtainable_reward + reward_diff;
        };

        user_vest.passed_time = user_vest.passed_time + (now - user_vest.lastet_updated);
        user_vest.lastet_updated = now;
    }

    #[test_only]
    fun init_vault(scenario:&mut Scenario,ctx:&mut TxContext):Vault{
        luck_vault::init_vault(ctx);
        next_tx(scenario, tx_context::sender(ctx));
        let v = test_scenario::take_shared<Vault>(scenario);
        let coin = coin::mint_for_testing<LUCK>(1000000000 * 1000,ctx);
        luck_vault::deposit_luck(&mut v,coin, ctx);
        v
    }

    #[test]
    fun test_verting() {
        let default_vester_amout: u64 = 1000000000 * 100;
        let day: u64 = 60 * 60 * 24 * 1000;


        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));
        let adm = admin::test_init(&mut ctx);
        let vault = init_vault(&mut scenario,&mut ctx);

        create_pool<ESLUCK>(&mut adm, day * 10, &mut ctx);
        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK>>(&mut scenario);
        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, default_vester_amout, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);
        next_tx(&mut scenario, sender);
        deposit<ESLUCK>(&mut pool,&mut vault, s, default_vester_amout, &clock, &mut ctx);
        clock::increment_for_testing(&mut clock, day);

        next_tx(&mut scenario, sender);
        claim<ESLUCK>(&mut pool, &mut vault,&clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let luck = test_scenario::take_from_sender<Coin<LUCK>>(&mut scenario);
        print(&coin::value(&luck));
        assert!(coin::value(&luck) == default_vester_amout / 10, 1001);
        assert!(pool.total_vesters == 1, 1002);
        assert!(pool.total_vested == (default_vester_amout as u256), 1003);

        test_utils::destroy(luck);

        next_tx(&mut scenario, sender);

        //TODO test for deposit twice
        let s_coin = esLuck::test_mint(&mut mintable, default_vester_amout, &mut ctx);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);
        deposit<ESLUCK>(&mut pool,&mut vault, s, default_vester_amout, &clock, &mut ctx);
        clock::increment_for_testing(&mut clock, day);
        next_tx(&mut scenario, sender);
        claim<ESLUCK>(&mut pool,&mut vault, &clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let luck = test_scenario::take_from_sender<Coin<LUCK>>(&mut scenario);

        assert!(pool.total_vested == ((default_vester_amout*2) as u256), 1006);
        assert!(coin::value(&luck) == default_vester_amout / 10 * 2, 1007);


        test_utils::destroy(luck);
        next_tx(&mut scenario, sender);

        clock::increment_for_testing(&mut clock, day * 9);
        claim<ESLUCK>(&mut pool, &mut vault,&clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let luck = test_scenario::take_from_sender<Coin<LUCK>>(&mut scenario);
        assert!(coin::value(&luck) == default_vester_amout * 2 - (default_vester_amout / 10 * 2), 1001);


        test_utils::destroy(mintable);
        test_utils::destroy(luck);
        test_utils::destroy(clock);
        test_utils::destroy(adm);

        test_utils::destroy(vault);
        test_scenario::return_shared(pool);
        end(scenario);
    }

    #[test]
    fun test_withdraw() {
        let default_vester_amout: u64 = 1000000000 * 100;
        let day: u64 = 60 * 60 * 24 * 1000;


        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(tx_context::sender(&mut ctx));
        let adm = admin::test_init(&mut ctx);

        let vault = init_vault(&mut scenario,&mut ctx);
        create_pool<ESLUCK>(&mut adm,day*10, &mut ctx);
        next_tx(&mut scenario, sender);

        let pool = test_scenario::take_shared<Pool<ESLUCK>>(&mut scenario);
        let mintable = esLuck::test_init(&mut ctx);
        let s_coin = esLuck::test_mint(&mut mintable, default_vester_amout, &mut ctx);
        let clock = clock::create_for_testing(&mut ctx);

        next_tx(&mut scenario, sender);
        let s = vector::empty<NonTransferCoin<ESLUCK>>();
        vector::push_back(&mut s, s_coin);
        deposit<ESLUCK>(&mut pool, &mut vault,s, default_vester_amout, &clock, &mut ctx);
        clock::increment_for_testing(&mut clock, day);
        withdraw<ESLUCK>(&mut pool, &mut vault,&clock, &mut ctx);
        next_tx(&mut scenario, sender);
        let luck = test_scenario::take_from_sender<Coin<LUCK>>(&mut scenario);
        print(&coin::value(&luck));
        assert!(coin::value(&luck) == default_vester_amout / 10, 1001);
        let s_coin = test_scenario::take_from_sender<NonTransferCoin<ESLUCK>>(&mut scenario);
        assert!(nonTransferCoin::value(&s_coin) == default_vester_amout - default_vester_amout / 10, 1001);

        test_utils::destroy(s_coin);
        test_utils::destroy(mintable);
        test_utils::destroy(luck);
        test_utils::destroy(clock);
        test_utils::destroy(adm);
        test_scenario::return_shared(pool);
        test_scenario::return_shared(vault);

        end(scenario);
    }
}
