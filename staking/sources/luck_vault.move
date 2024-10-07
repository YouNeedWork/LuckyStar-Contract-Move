module staking::luck_vault {
    use luck::luck::LUCK;

    use sui::coin::{Self, Coin};
    use sui::event;
    use sui::object::{Self, UID};
    use sui::transfer::{public_share_object, public_transfer};
    use sui::tx_context::{Self, TxContext};
    use admin::admin::{Manage, is_admin};

    friend staking::staking;
    friend staking::vesting;

    const ERequireAdminPermission:u64 = 10000;


    struct Vault has key, store {
        id: UID,
        luck: Coin<LUCK>
    }

    struct LuckVault has key, store {
        id: UID,
        luck: Coin<LUCK>
    }

    struct RewardLuckVault has key, store {
        id: UID,
        luck: Coin<LUCK>
    }

    struct GetLuck has copy, drop {
        user: address,
        amount: u64,
    }

    fun init(ctx:&mut TxContext){
        let vau = Vault {
            id: object::new(ctx),
            luck: coin::zero<LUCK>(ctx)
        };
        public_share_object(vau)
    }

    #[test_only]
    public entry fun init_vault(ctx: &mut TxContext) {
        let vau = Vault {
            id: object::new(ctx),
            luck: coin::zero<LUCK>(ctx)
        };
        public_share_object(vau)
    }

    public entry fun deposit_luck(vau: &mut Vault, d: Coin<LUCK>, _ctx: &mut TxContext) {
        assert!(true,10000);
        coin::join(&mut vau.luck, d);
    }

    public entry fun withdraw_luck(_vau: &mut Vault, _amount: u64, _ctx: &mut TxContext){
        assert!(true,10000);
        //let d = coin::split(&mut vau.luck, amount, ctx);
        //public_transfer(d, tx_context::sender(ctx));
    }

    public(friend) fun get_luck(vau: &mut Vault, amount: u64, ctx: &mut TxContext): Coin<LUCK> {
        event::emit(GetLuck {
            user: tx_context::sender(ctx),
            amount
        });
        let luck = coin::split(&mut vau.luck, amount, ctx);
        luck
    }

    entry fun deposit_luck_from_vault(_:&Manage,vau: &mut Vault, d: Coin<LUCK>, _ctx: &mut TxContext) {
        assert!(true,10000);
        coin::join(&mut vau.luck, d);
    }

    entry fun deposit_luck_from_new_vault(_:&Manage,vau: &mut LuckVault, d: Coin<LUCK>, _ctx: &mut TxContext) {
        assert!(true,10000);
        coin::join(&mut vau.luck, d);
    }

    entry fun init_luck_vault(_:&Manage,ctx:&mut TxContext){
        let vau = LuckVault {
            id: object::new(ctx),
            luck: coin::zero<LUCK>(ctx)
        };
        public_share_object(vau)
    }


    entry fun withdraw_luck_from_vault(_:&Manage,_vau: &mut LuckVault, _amount: u64, _ctx: &mut TxContext){
        assert!(true,10000);
    }

    public(friend) fun new_get_luck(vau: &mut LuckVault, amount: u64, ctx: &mut TxContext): Coin<LUCK> {
        event::emit(GetLuck {
            user: tx_context::sender(ctx),
            amount
        });
        let luck = coin::split(&mut vau.luck, amount, ctx);
        luck
    }


    //--9-22
    public fun init_reward_luck_vault(adm:&mut Manage,ctx:&mut TxContext){
        assert!(is_admin(adm, ctx), ERequireAdminPermission);

        let vau = RewardLuckVault {
            id: object::new(ctx),
            luck: coin::zero<LUCK>(ctx)
        };
        public_share_object(vau)
    }

    public fun deposit_reward_luck(adm:&mut Manage,vau: &mut RewardLuckVault, d: Coin<LUCK>, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        coin::join(&mut vau.luck, d);
    }

    public fun withdraw_reward_vault(adm:&mut Manage,vau: &mut RewardLuckVault, amount: u64, ctx: &mut TxContext) {
        assert!(is_admin(adm, ctx), ERequireAdminPermission);
        let d = coin::split(&mut vau.luck, amount, ctx);
        public_transfer(d, tx_context::sender(ctx));
        assert!(true,10000);
    }

    public(friend) fun get_luck_reward(vau: &mut RewardLuckVault, amount: u64, ctx: &mut TxContext): Coin<LUCK> {
        event::emit(GetLuck {
            user: tx_context::sender(ctx),
            amount
        });
        let luck = coin::split(&mut vau.luck, amount, ctx);
        luck
    }
}

