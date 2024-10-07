module games::xluck_reward {
    use sui::object::{Self, UID};
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::{Self, TxContext};
    use token::nonTransferCoin;
    use nft::lucky::{LuckyNFT, level, point,point_up};
    use newnft::lucky::{LuckyNFT as NewLuckNFT,LevelCap, point_up as new_point_up, level as new_level};


    use std::option::{Option, none, some};
    use sui::bag::Bag;
    use sui::bag;


    use games::random;
    use token::nonTransferCoin::NonTransferCoin;
    use admin::admin::{is_admin, Manage};
    #[test_only]
    use xluck::xLuck;
    #[test_only]
    use xluck::xLuck::XLUCK;
    #[test_only]
    use sui::test_scenario;
    #[test_only]
    use sui::test_scenario::{next_tx, end};
    #[test_only]
    use sui::test_utils;
    use std::option;
    #[test_only]
    use nft::lucky::{mint_for_test};



    friend games::game_controller;

    const DECIMAL:  u64 = 1000000000;
    const ERequireAdminPermission: u64 = 1005;
    const ENFTAlreadyStaked:u64 = 1006;
    const ENFTNotStaked:u64=1007;
    const VERSION:u64 = 1;

    struct NewReward<phantom T> has key, store {
        id: UID,
        xluck_supply: u64,
        low:u64,
        hight:u64,
        x_luck:NonTransferCoin<T>,
        nfts:Bag,
        version:u64,
        cap:LevelCap,
    }

    struct Reward<phantom T> has key, store {
        id: UID,
        xluck_supply: u64,
        low:u64,
        hight:u64,
        x_luck:NonTransferCoin<T>,
        nfts:Bag,
    }

    public entry fun create_reward<T>(lp: NonTransferCoin<T>,low:u64,hight:u64, ctx: &mut TxContext) {
        public_share_object(Reward<T>{id: object::new(ctx),low , hight, xluck_supply: 0, x_luck: lp,nfts:bag::new(ctx)});
    }

    public entry fun create_luck_rate<T>(r: &mut Reward<T>,adm:&mut Manage,low:u64,hight:u64, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        r.hight = hight;
        r.low = low;
    }

    public entry fun add_luck<T>(r: &mut NewReward<T>,adm:&mut Manage,xluck: NonTransferCoin<T>, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        nonTransferCoin::join(&mut r.x_luck, xluck);
    }

    public(friend) fun get_reward<T>(_r:&mut Reward<T>,_seed:vector<u8>,_bet_amount:u64,_sender:address,_ctx:&mut TxContext):(u64,u64){
        assert!(false,ERequireAdminPermission);
        (0,0)
    }

    public entry fun stake_nft<T>(r: &mut Reward<T>,nft:LuckyNFT,ctx:&mut TxContext) {
        let sender = tx_context::sender(ctx);
        assert!(!bag::contains(&r.nfts,sender), ENFTAlreadyStaked);
        bag::add(&mut r.nfts,sender,nft);
    }

    public entry fun unstake_nft<T>(r: &mut Reward<T>,ctx:&mut TxContext){
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&r.nfts,sender), ENFTNotStaked);
        let nft = bag::remove<address,LuckyNFT>(&mut r.nfts,sender);
        public_transfer(nft,sender);
    }

    public fun add_point<T>(r: &mut Reward<T>,point:u64,sender:address,ctx:&mut TxContext) {
        if (bag::contains(&r.nfts,sender)) {
            let nft = bag::borrow_mut<address,LuckyNFT>(&mut r.nfts,sender);
            point_up(nft,point,ctx);
        }
    }

    public fun get_boost<T>(r: &mut Reward<T>,sender:address):u64{
        let nft = get_nft_level(r,sender);
        if (option::is_some(&nft)) {
            let level = option::extract(&mut nft);

            if (level == 2) {
                10
            } else if (level == 3) {
                20
            }  else if (level == 4) {
                30
            } else if (level == 5) {
                50
            } else {
                0
            }
        } else {
             0
        }
    }

    public fun get_nft_level<T>(r: &mut Reward<T>,sender:address):Option<u64> {

        if (bag::contains(&r.nfts,sender)) {
            let nft = bag::borrow<address,LuckyNFT>(&mut r.nfts,sender);
            some(level(nft))
        } else {
            none()
        }
    }

    public fun get_nft_point<T>(r: &mut Reward<T>,sender:address):Option<u64> {
        if (bag::contains(&r.nfts,sender)) {
            let nft = bag::borrow<address,LuckyNFT>(&mut r.nfts,sender);
            some(point(nft))
        } else {
            none()
        }
    }

    // migration
    public entry fun migrate<T>(r: &mut Reward<T>,adm:&mut Manage,cap:LevelCap,ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        // let Reward<T>{
        //     id,
        //     low,
        //     hight,
        //     xluck_supply,
        //     x_luck,
        //     nfts,
        // } = r;
        // object::delete(id);
        let v = nonTransferCoin::value(&r.x_luck);

        public_share_object(NewReward<T>{
            id:object::new(ctx),
            low:r.low,
            hight:r.hight,
            xluck_supply:r.xluck_supply,
            x_luck:nonTransferCoin::split(&mut r.x_luck,tx_context::sender(ctx),v,ctx),
            nfts:bag::new(ctx),
            version:VERSION,
            cap,
        })
    }


    public(friend) fun new_get_reward<T>(r:&mut NewReward<T>,seed:vector<u8>,bet_amount:u64,sender:address,ctx:&mut TxContext):(u64,u64){
        if (!bag::contains(&r.nfts,sender)) {
            return (0,0)
        };

        let number = random::rand_u64_range_with_seed(seed,r.low,r.hight);
        new_add_point<T>(r,bet_amount,sender,ctx);

        let b = get_new_boost<T>(r,sender);
        let boost = number + (number * b / 100);
        let win = ((bet_amount as u256)*(boost as u256) / (DECIMAL as u256) as u64);

        r.xluck_supply = r.xluck_supply + win;
        let reward = nonTransferCoin::split(&mut r.x_luck, sender,win, ctx);
        public_transfer(reward,sender);
        (win,b)
    }

    public entry fun nft_stake<T>(r: &mut NewReward<T>,nft:NewLuckNFT,ctx:&mut TxContext) {
        let sender = tx_context::sender(ctx);
        assert!(!bag::contains(&r.nfts,sender), ENFTAlreadyStaked);
        bag::add(&mut r.nfts,sender,nft);
    }

    public entry fun nft_unstake<T>(r: &mut NewReward<T>,ctx:&mut TxContext){
        let sender = tx_context::sender(ctx);
        assert!(bag::contains(&r.nfts,sender), ENFTNotStaked);
        let nft = bag::remove<address,NewLuckNFT>(&mut r.nfts,sender);
        public_transfer(nft,sender);
    }

    public entry fun change_luck_rate<T>(r: &mut NewReward<T>,adm:&mut Manage,low:u64,hight:u64, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        r.hight = hight;
        r.low = low;
    }

    fun new_add_point<T>(r: &mut NewReward<T>,point:u64,sender:address,ctx:&mut TxContext) {
        if (bag::contains(&r.nfts,sender)) {
            let nft = bag::borrow_mut<address,NewLuckNFT>(&mut r.nfts,sender);
            new_point_up(&r.cap,nft,point,ctx);
        }
    }


    public fun get_new_boost<T>(r: &mut NewReward<T>,sender:address):u64{
        let nft = new_get_nft_level(r,sender);
        if (option::is_some(&nft)) {
            let level = option::extract(&mut nft);

            if (level == 2) {
                10
            } else if (level == 3) {
                20
            }  else if (level == 4) {
                30
            } else if (level == 5) {
                50
            } else {
                0
            }
        } else {
            0
        }
    }


    public fun new_get_nft_level<T>(r: &mut NewReward<T>,sender:address):Option<u64> {
        if (bag::contains(&r.nfts,sender)) {
            let nft = bag::borrow<address,NewLuckNFT>(&mut r.nfts,sender);
            some(new_level(nft))
        } else {
            none()
        }
    }

    #[test]
    fun test_get_reward(){
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&ctx);
        let seed = b"12312312312312312312313213123";

        let scenario = test_scenario::begin(sender);
        let mintable = xLuck::test_init(&mut ctx);
        let r_coin = xLuck::test_mint(&mut mintable, 10000000000000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 100, 1000, &mut ctx);
        next_tx(&mut scenario, sender);
        let reward = test_scenario::take_shared<Reward<XLUCK>>(&mut scenario);
        let (r,_) =  get_reward(&mut reward,seed,100,sender,&mut ctx);
        assert!(r == 0,1);

        let nft = mint_for_test(&mut ctx);
        stake_nft(&mut reward, nft, &mut ctx);

        let (r,muti) =  get_reward(&mut reward,seed,1000*1000000000,sender,&mut ctx);
        assert!(r >0,1);
        assert!(muti == 10,1);
        let (r,muti) =  get_reward(&mut reward,seed,1000*1000000000,sender,&mut ctx);
        assert!(r >=0,1);
        assert!(muti == 20,1);
        let (r,muti) =  get_reward(&mut reward,seed,2000*1000000000,sender,&mut ctx);
        assert!(r >=0,1);
        assert!(muti == 30,1);
        let (r,muti) =  get_reward(&mut reward,seed,4000*1000000000,sender,&mut ctx);
        assert!(r >=0,1);
        assert!(muti == 50,1);


        test_utils::destroy(mintable);
        test_utils::destroy(reward);

        end(scenario);
    }

    #[test]
    #[expected_failure(abort_code = ENFTAlreadyStaked)]
    fun test_stake_twice() {
        let ctx = tx_context::dummy();
        let sender = tx_context::sender(&ctx);
        let seed = b"12312312312312312312313213123";

        let scenario = test_scenario::begin(sender);
        let mintable = xLuck::test_init(&mut ctx);
        let r_coin = xLuck::test_mint(&mut mintable, 10000000000000000000, &mut ctx);
        create_reward<XLUCK>(r_coin, 100, 1000, &mut ctx);
        next_tx(&mut scenario, sender);
        let reward = test_scenario::take_shared<Reward<XLUCK>>(&mut scenario);
        let (r,_) =  get_reward(&mut reward,seed,100,sender,&mut ctx);
        assert!(r == 0,1);

        let nft = mint_for_test(&mut ctx);
        stake_nft(&mut reward, nft, &mut ctx);

        let (r,muti) =  get_reward(&mut reward,seed,1000*1000000000,sender,&mut ctx);
        assert!(r >0,1);
        assert!(muti == 10,1);
        let (r,muti) =  get_reward(&mut reward,seed,1000*1000000000,sender,&mut ctx);
        assert!(r >=0,1);
        assert!(muti == 20,1);
        let (r,muti) =  get_reward(&mut reward,seed,2000*1000000000,sender,&mut ctx);
        assert!(r >=0,1);
        assert!(muti == 30,1);
        let (r,muti) =  get_reward(&mut reward,seed,4000*1000000000,sender,&mut ctx);
        assert!(r >=0,1);
        assert!(muti == 50,1);

        let nft = mint_for_test(&mut ctx);
        stake_nft(&mut reward, nft, &mut ctx);

        test_utils::destroy(mintable);
        test_utils::destroy(reward);

        end(scenario);
    }
}
