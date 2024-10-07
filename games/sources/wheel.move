module games::wheel {
    use sui::coin::Coin;
    use sui::tx_context;
    use sui::tx_context::TxContext;
    use sui::coin;

    use games::vault::{Self, Vault, check_pool_amount};
    #[test_only]
    use sui::test_scenario;
    #[test_only]
    use games::vault::{create_vault, add_liquidity, pool_amount};
    #[test_only]
    use sui::test_scenario::{next_tx, end};
    #[test_only]
    use llp::llp::LLP;
    #[test_only]
    use sui::sui::SUI;
    use utils::utils;
    use sui::pay;

    #[test_only]
    use std::vector;
    #[test_only]
    use xluck::xLuck;
    #[test_only]
    use games::xluck_reward::{create_reward, Reward};
    #[test_only]
    use xluck::xLuck::XLUCK;
    #[test_only]
    use sui::test_utils;
    use games::game_controller;
    use games::game_controller::Controller;
    use sui::clock::Clock;

    #[test_only]
    use sui::clock;
    #[test_only]
    use games::game_controller::provide;
    #[test_only]
    use std::debug::print;

    const GAME_ID:u64 = 4;

    const EGameAmountTooLager:u64 = 1001;

    public entry fun play<T, LLP>(
        v: &mut Vault<T, LLP>,
        c: &mut Controller,
        all: vector<Coin<T>>,
        amount: u64,
        number: u64,
        clock:&Clock,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);
        assert!(number == 2 || number == 3 || number == 6 || number == 48, 1005);

        let paid = coin::zero<T>(ctx);
        pay::join_vec(&mut paid, all);


        let fee = amount * vault::get_player_fee(v) / 10000;
        assert!(coin::value(&paid) >= amount + fee, 1);

        if (number == 2){
            assert!(check_pool_amount(v,amount),EGameAmountTooLager);
        } else if (number ==3){
            assert!(check_pool_amount(v,amount*2),EGameAmountTooLager);
        } else if (number == 6){
            assert!(check_pool_amount(v,amount*5),EGameAmountTooLager);
        } else {
            assert!(check_pool_amount(v,amount*47),EGameAmountTooLager);
        };


        let all = coin::split(&mut paid, amount + fee, ctx);
        let bet = vault::collect_player_fee(v, all,amount, ctx);
        utils::destroy_zero_or_transfer(paid, ctx);
        vault::take_bet<T, LLP>(v, bet);

        game_controller::new_game(c, clock, sender, amount, number, GAME_ID, ctx);
    }

    #[test_only]
    const START_TIME:u64 = 1595431050*1000;

    #[test]
    #[expected_failure(abort_code = game_controller::EGameAlreadyCompleted)]
    fun test_play_wheel_with_open_twice() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(sender);

        let mintable = xLuck::test_init(&mut ctx);
        let r_coin = xLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 100000, 10000000, &mut ctx);
        next_tx(&mut scenario, sender);

        let llp = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let sui = coin::mint_for_testing<SUI>(1000000000000000, &mut ctx);
        create_vault<SUI, LLP>(llp, &mut ctx);
        next_tx(&mut scenario, sender);
        let vault = test_scenario::take_shared<Vault<SUI, LLP>>(&mut scenario);
        add_liquidity(&mut vault, sui, &mut ctx);
        next_tx(&mut scenario, sender);

        let game_ctl = game_controller::test_init(&mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        clock::set_for_testing(&mut clock, START_TIME);


        let s = coin::mint_for_testing<SUI>(10200000, &mut ctx);
        let all = vector::empty<Coin<SUI>>();
        vector::push_back(&mut all, s);
        play(&mut vault, &mut game_ctl, all, 10000000, 2, &clock,&mut ctx);
        let sig = x"8d61d9100567de44682506aea1a7a6fa6e5491cd27a0a0ed349ef6910ac5ac20ff7bc3e09d7c046566c9f7f3c6f3b10104990e7cb424998203d8f7de586fb7fa5f60045417a432684f85093b06ca91c769f0e7ca19268375e659c2a2352b4655";
        let prev_sig = x"176f93498eac9ca337150b46d21dd58673ea4e3581185f869672e59fa4cb390a";

        let r_coin = xLuck::test_mint(&mut mintable, 10000000000000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 10000000000, 1000000000000, &mut ctx);
        next_tx(&mut scenario, sender);
        let r = test_scenario::take_shared<Reward<XLUCK>>(&mut scenario);

        provide(&mut vault,&mut game_ctl, &mut r,&clock,sig,prev_sig,1, &mut ctx);
        next_tx(&mut scenario, sender);

        //lost
        assert!(pool_amount(&vault) == 990000010000000, 10002);



        let s = coin::mint_for_testing<SUI>(10200000, &mut ctx);
        let all = vector::empty<Coin<SUI>>();
        vector::push_back(&mut all, s);
        play(&mut vault, &mut game_ctl, all, 10000000, 6, &clock,&mut ctx);
        let sig = x"8d61d9100567de44682506aea1a7a6fa6e5491cd27a0a0ed349ef6910ac5ac20ff7bc3e09d7c046566c9f7f3c6f3b10104990e7cb424998203d8f7de586fb7fa5f60045417a432684f85093b06ca91c769f0e7ca19268375e659c2a2352b4655";
        let prev_sig = x"176f93498eac9ca337150b46d21dd58673ea4e3581185f869672e59fa4cb390a";

        provide(&mut vault,&mut game_ctl,&mut r, &clock,sig,prev_sig,1, &mut ctx);
        next_tx(&mut scenario, sender);
        print(&pool_amount(&vault));

        test_utils::destroy(mintable);
        test_utils::destroy(game_ctl);
        test_utils::destroy(clock);
        test_utils::destroy(r);

        test_scenario::return_shared(vault);
        end(scenario);
    }

    #[test]
    fun test_play_wheel_with_lost() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(sender);

        let mintable = xLuck::test_init(&mut ctx);
        let r_coin = xLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 100000, 10000000, &mut ctx);
        next_tx(&mut scenario, sender);

        let llp = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let sui = coin::mint_for_testing<SUI>(1000000000000000, &mut ctx);
        create_vault<SUI, LLP>(llp, &mut ctx);
        next_tx(&mut scenario, sender);
        let vault = test_scenario::take_shared<Vault<SUI, LLP>>(&mut scenario);
        add_liquidity(&mut vault, sui, &mut ctx);
        next_tx(&mut scenario, sender);

        let game_ctl = game_controller::test_init(&mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        clock::set_for_testing(&mut clock, START_TIME);


        let s = coin::mint_for_testing<SUI>(10200000, &mut ctx);
        let all = vector::empty<Coin<SUI>>();
        vector::push_back(&mut all, s);
        play(&mut vault, &mut game_ctl, all, 10000000, 2, &clock,&mut ctx);
        let sig = x"8d61d9100567de44682506aea1a7a6fa6e5491cd27a0a0ed349ef6910ac5ac20ff7bc3e09d7c046566c9f7f3c6f3b10104990e7cb424998203d8f7de586fb7fa5f60045417a432684f85093b06ca91c769f0e7ca19268375e659c2a2352b4655";
        let prev_sig = x"176f93498eac9ca337150b46d21dd58673ea4e3581185f869672e59fa4cb390a";

        let r_coin = xLuck::test_mint(&mut mintable, 10000000000000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 10000000000, 1000000000000, &mut ctx);
        next_tx(&mut scenario, sender);
        let r = test_scenario::take_shared<Reward<XLUCK>>(&mut scenario);

        provide(&mut vault,&mut game_ctl,&mut r, &clock,sig,prev_sig,1, &mut ctx);
        next_tx(&mut scenario, sender);

        //lost
        assert!(pool_amount(&vault) == 990000010000000, 10002);

        test_utils::destroy(mintable);
        test_utils::destroy(game_ctl);
        test_utils::destroy(clock);
        test_utils::destroy(r);

        test_scenario::return_shared(vault);
        end(scenario);
    }

    #[test]
    fun test_play_wheel_with_win() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(sender);

        let mintable = xLuck::test_init(&mut ctx);
        let r_coin = xLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 100000, 10000000, &mut ctx);
        next_tx(&mut scenario, sender);

        let llp = coin::mint_for_testing<LLP>(1000000000000000, &mut ctx);
        let sui = coin::mint_for_testing<SUI>(1000000000000000, &mut ctx);
        create_vault<SUI, LLP>(llp, &mut ctx);
        next_tx(&mut scenario, sender);
        let vault = test_scenario::take_shared<Vault<SUI, LLP>>(&mut scenario);
        add_liquidity(&mut vault, sui, &mut ctx);
        next_tx(&mut scenario, sender);

        let game_ctl = game_controller::test_init(&mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        clock::set_for_testing(&mut clock, START_TIME);


        let s = coin::mint_for_testing<SUI>(10200000, &mut ctx);
        let all = vector::empty<Coin<SUI>>();
        vector::push_back(&mut all, s);
        play(&mut vault, &mut game_ctl, all, 10000000, 6, &clock,&mut ctx);
        let sig = x"8d61d9100567de44682506aea1a7a6fa6e5491cd27a0a0ed349ef6910ac5ac20ff7bc3e09d7c046566c9f7f3c6f3b10104990e7cb424998203d8f7de586fb7fa5f60045417a432684f85093b06ca91c769f0e7ca19268375e659c2a2352b4655";
        let prev_sig = x"176f93498eac9ca337150b46d21dd58673ea4e3581185f869672e59fa4cb390a";

        let r_coin = xLuck::test_mint(&mut mintable, 10000000000000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 10000000000, 1000000000000, &mut ctx);
        next_tx(&mut scenario, sender);
        let r = test_scenario::take_shared<Reward<XLUCK>>(&mut scenario);

        provide(&mut vault,&mut game_ctl, &mut r,&clock,sig,prev_sig,1, &mut ctx);
        next_tx(&mut scenario, sender);
        assert!(pool_amount(&vault) == (990000000000000 - 50000000), 10002);

        test_utils::destroy(mintable);
        test_utils::destroy(game_ctl);
        test_utils::destroy(clock);
        test_utils::destroy(r);

        test_scenario::return_shared(vault);
        end(scenario);
    }


    #[test]
    #[expected_failure(abort_code = EGameAmountTooLager)]
    fun test_play_wheel_with_max_amount() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&mut ctx);
        let scenario = test_scenario::begin(sender);

        let mintable = xLuck::test_init(&mut ctx);
        let r_coin = xLuck::test_mint(&mut mintable, 100000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 100000, 10000000, &mut ctx);
        next_tx(&mut scenario, sender);

        let llp = coin::mint_for_testing<LLP>(10000 * 1000000000, &mut ctx);
        let sui = coin::mint_for_testing<SUI>(10000 * 1000000000, &mut ctx);
        create_vault<SUI, LLP>(llp, &mut ctx);
        next_tx(&mut scenario, sender);
        let vault = test_scenario::take_shared<Vault<SUI, LLP>>(&mut scenario);
        add_liquidity(&mut vault, sui, &mut ctx);
        next_tx(&mut scenario, sender);

        let game_ctl = game_controller::test_init(&mut ctx);
        let clock = clock::create_for_testing(&mut ctx);
        clock::set_for_testing(&mut clock, START_TIME);

        //10000 * 0.01 = 100 /47 = 2  so this fine
        let s = coin::mint_for_testing<SUI>(22 * 100000000, &mut ctx);
        let all = vector::empty<Coin<SUI>>();
        vector::push_back(&mut all, s);
        play(&mut vault, &mut game_ctl, all, 2 * 1000000000, 6, &clock,&mut ctx);
        //12 * 47 = 564 = %5  so got this fail
        let s = coin::mint_for_testing<SUI>(12 * 1000000000, &mut ctx);
        let all = vector::empty<Coin<SUI>>();
        vector::push_back(&mut all, s);
        play(&mut vault, &mut game_ctl, all, 10 * 1000000000, 48, &clock,&mut ctx);
        let sig = x"8d61d9100567de44682506aea1a7a6fa6e5491cd27a0a0ed349ef6910ac5ac20ff7bc3e09d7c046566c9f7f3c6f3b10104990e7cb424998203d8f7de586fb7fa5f60045417a432684f85093b06ca91c769f0e7ca19268375e659c2a2352b4655";
        let prev_sig = x"176f93498eac9ca337150b46d21dd58673ea4e3581185f869672e59fa4cb390a";

        let r_coin = xLuck::test_mint(&mut mintable, 10000000000000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 10000000000, 1000000000000, &mut ctx);
        next_tx(&mut scenario, sender);
        let r = test_scenario::take_shared<Reward<XLUCK>>(&mut scenario);

        provide(&mut vault,&mut game_ctl, &mut r,&clock,sig,prev_sig,1, &mut ctx);
        next_tx(&mut scenario, sender);


        test_utils::destroy(mintable);
        test_utils::destroy(game_ctl);
        test_utils::destroy(clock);
        test_utils::destroy(r);

        test_scenario::return_shared(vault);
        end(scenario);
    }
}
