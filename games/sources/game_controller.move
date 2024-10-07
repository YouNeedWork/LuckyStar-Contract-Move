module games::game_controller {
    use games::drand;
    use games::random;
    use games::vault::{Self, Vault};
    use games::xluck_reward::{Reward, NewReward, new_get_reward};
    use sui::bag::{Self, Bag};
    use sui::clock::{Self, Clock};
    use sui::coin;
    use sui::event;
    use sui::math;
    use sui::object::{Self, UID};
    use sui::table_vec::{Self, TableVec};
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::TxContext;

    const GAME_COIN_FLIP: u64 = 1;
    const GAME_RAFFLE: u64 = 2;
    const GAME_RANGE: u64 = 3;
    const GAME_WHELL: u64 = 4;


    const Opened: u64 = 0;
    const Completed: u64 = 1;

    const EGameAlreadyCompleted: u64 = 2;
    const ERoundNotFound: u64 = 3;

    const EDELETE:u64=10001;

    friend games::coinFlip;
    friend games::raffle;
    friend games::range;
    friend games::wheel;


    struct Game has key, store {
        id: UID,
        player: address,
        amount: u64,
        bet: u64,
        game: u64,
    }

    struct BetEvent has copy, drop {
        player: address,
        amount: u64,
        bet: u64,
        game: u64,
        round: u64,
    }

    struct GamePlay has copy, drop {
        game_id: u64,
        player: address,
        amount: u64,
        result: u64,
        random_number: u64,
        profit: u64,
        reward: u64,
        boost: u64,
    }

    struct Round has key, store {
        id: UID,
        games: TableVec<Game>,
        status: u64,
    }

    struct Controller has key, store {
        id: UID,
        rounds: Bag,
    }

    fun init(ctx: &mut TxContext) {
        let ctl = Controller {
            id: object::new(ctx),
            rounds: bag::new(ctx),
        };
        public_share_object(ctl);
    }

    #[test_only]
    public fun test_init(ctx: &mut TxContext): Controller {
        let ctl = Controller {
            id: object::new(ctx),
            rounds: bag::new(ctx),
        };
        ctl
    }

    public(friend) fun new_game(
        ctl: &mut Controller,
        clock: &Clock,
        player: address,
        amount: u64,
        bet: u64,
        game: u64,
        ctx: &mut TxContext
    ) {
        let game_play = Game {
            id: object::new(ctx),
            player,
            amount,
            bet,
            game,
        };

        let timestamp = (clock::timestamp_ms(clock) / 1000);

        let currently_round = ((timestamp - drand::get_genesis_time(
        )) / 30) + 2;//this shuold be +2 in case when the timestamp not update yet

        if (bag::contains(&ctl.rounds, currently_round)) {
            let round = bag::borrow_mut<u64, Round>(&mut ctl.rounds, currently_round);
            table_vec::push_back(&mut round.games, game_play);
        } else {
            let games = table_vec::empty<Game>(ctx);
            table_vec::push_back(&mut games, game_play);

            let round = Round {
                id: object::new(ctx),
                games,
                status: Opened,
            };

            bag::add(&mut ctl.rounds, currently_round, round);
        };

        let event = BetEvent {
            player,
            amount,
            bet,
            game,
            round: currently_round,
        };

        event::emit(event);
    }

    public entry fun provide<T, LLP, XLUCK>(
        _v: &mut Vault<T, LLP>,
        _ctl: &mut Controller,
        _r: &mut Reward<XLUCK>,
        _clock: &Clock,
        _drand_sig: vector<u8>,
        _drand_prev_sig: vector<u8>,
        _round: u64,
        _ctx: &mut TxContext
    ) {
        assert!(false,EDELETE);
    }

    public entry fun provide_with_nft<T, LLP, XLUCK>(
        v: &mut Vault<T, LLP>,
        ctl: &mut Controller,
        r: &mut NewReward<XLUCK>,
        _clock: &Clock,
        drand_sig: vector<u8>,
        drand_prev_sig: vector<u8>,
        round: u64,
        ctx: &mut TxContext
    ) {
        drand::verify_drand_signature(drand_sig, drand_prev_sig, round);
        let digest = drand::derive_randomness(drand_sig);
        assert!(bag::contains(&ctl.rounds, round), ERoundNotFound);
        let round = bag::borrow_mut<u64, Round>(&mut ctl.rounds, round);
        assert!(round.status != Completed, EGameAlreadyCompleted);
        round.status = Completed;

        let len: u64 = table_vec::length(&round.games);
        let i: u64 = 0;
        while (i < len) {
            let game = table_vec::borrow(&round.games, i);
            if (game.game == GAME_COIN_FLIP) {
                coin_flip<T, LLP, XLUCK>(v, r, game.player, game.amount, game.bet, digest, ctx);
            } else if (game.game == GAME_RAFFLE) {
                raffle<T, LLP, XLUCK>(v, r, game.player, game.amount, game.bet, digest, ctx);
            } else if (game.game == GAME_RANGE) {
                range<T, LLP, XLUCK>(v, r, game.player, game.amount, game.bet, digest, ctx);
            } else if (game.game == GAME_WHELL) {
                wheel<T, LLP, XLUCK>(v, r, game.player, game.amount, game.bet, digest, ctx);
            };

            i = i + 1;
        }
    }

    fun coin_flip<T, LLP, XLUCK>(
        v: &mut Vault<T, LLP>,
        r: &mut NewReward<XLUCK>,
        player: address,
        amount: u64,
        number: u64,
        digest: vector<u8>,
        ctx: &mut TxContext
    ) {
        let random_number = random::rand_u64_range_with_seed(digest, 0, 99);
        let result: u64 = 0;
        let profit: u64 = 0;

        if ((number == 0 && random_number < 49) || (number == 1 && random_number > 50)) {
            //win
            result = 1;
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win = vault::lose<T, LLP>(v, bet, ctx);
            profit = coin::value(&win);
            public_transfer(win, player);
        };

        let (reward, boost) = new_get_reward(r,digest, amount, player, ctx);
        event::emit(GamePlay {
            game_id: GAME_COIN_FLIP,
            player,
            amount,
            result,
            random_number,
            profit,
            reward,
            boost
        })
    }

    fun raffle<T, LLP, XLUCK>(
        v: &mut Vault<T, LLP>,
        r: &mut NewReward<XLUCK>,
        player: address,
        amount: u64,
        number: u64,
        digest: vector<u8>,
        ctx: &mut TxContext
    ) {
        let random_number = random::rand_u64_range_with_seed(digest, 0, 99);
        let result: u64 = 0;
        let profit: u64 = 0;

        if ((number == 0 && random_number < 49) || (number == 1 && random_number > 50)) {
            //win
            result = 1;
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win = vault::lose<T, LLP>(v, bet, ctx);
            profit = coin::value(&win);

            public_transfer(win, player);
        };

        let (reward, boost) = new_get_reward(r,digest, amount, player, ctx);
        event::emit(GamePlay {
            game_id: GAME_RAFFLE,
            player,
            amount,
            result,
            random_number,
            profit,
            reward,
            boost
        })
    }

    fun range<T, LLP, XLUCK>(
        v: &mut Vault<T, LLP>,
        r: &mut NewReward<XLUCK>,
        player: address,
        amount: u64,
        number: u64,
        digest: vector<u8>,
        ctx: &mut TxContext
    ) {
        let random_number = random::rand_u64_range_with_seed(digest, 0, 99);
        let result: u64 = 0;
        let profit: u64 = 0;
        if (random_number <= 95) {
            random_number = random_number + 2;
        };

        if (number >= random_number) {
            //win
            result = 1;
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win_amount = math::divide_and_round_up(
                (amount * math::divide_and_round_up(100 * 10000, number)),
                10000
            ) - amount;
            //win
            let win = vault::lose_amount<T, LLP>(v, bet, win_amount, ctx);
            profit = coin::value(&win);
            public_transfer(win, player);
        };

        let (reward, boost) = new_get_reward(r,digest, amount, player, ctx);
        event::emit(GamePlay {
            game_id: GAME_RANGE,
            player,
            amount,
            result,
            random_number,
            profit,
            reward,
            boost
        })
    }

    fun wheel<T, LLP, XLUCK>(
        v: &mut Vault<T, LLP>,
        r: &mut NewReward<XLUCK>,
        player: address,
        amount: u64,
        number: u64,
        digest: vector<u8>,
        ctx: &mut TxContext
    ) {
        let result: u64 = 0;
        let profit: u64 = 0;

        let random_number = random::rand_u64_range_with_seed(digest, 0, 4900);
        if ((number == 2) && (random_number < 2352)) {
            result = 1;
            //win
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win = vault::lost_multiple_times<T, LLP>(v, bet, number, ctx);
            profit = coin::value(&win);
            public_transfer(win, player);
        } else if ((number == 3) && (random_number >= 2400 && random_number < 3968)) {
            result = 1;
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win = vault::lost_multiple_times<T, LLP>(v, bet, number, ctx);
            profit = coin::value(&win);
            public_transfer(win, player);
        } else if ((number == 6) && (random_number >= 4000 && random_number < 4784)) {
            result = 1;
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win = vault::lost_multiple_times<T, LLP>(v, bet, number, ctx);
            profit = coin::value(&win);
            public_transfer(win, player);
        } else if ((number == 48) && (random_number >= 4800)) {
            result = 1;
            let bet = vault::return_bet<T, LLP>(v, amount, ctx);
            let win = vault::lost_multiple_times<T, LLP>(v, bet, number, ctx);
            profit = coin::value(&win);
            public_transfer(win, player);
        };

        let (reward, boost) = new_get_reward(r,digest, amount, player, ctx);

        event::emit(GamePlay {
            game_id: GAME_WHELL,
            player,
            amount,
            result,
            random_number,
            profit,
            reward,
            boost
        })
    }
}
