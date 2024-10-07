# readme

## todo
- [X] add test for staking
- [X] split all the diffent pool into different module
- [X] add test for vesting
- [X] when user play game for reward(XLUCK)
- [X] add test for games
- [X] change u64 to u256 for all store
- [X] Change vec type to dyn type 
- [X] Add error code for all modules
- [X] fix all tests
- [ ] Add event to all struct change function
- [X] add nft level up function,change reward function to reward XLUCK when user have nft



分割COIN 只有标准coin可以使用
```bash
sui client split-coin --count 5 --coin-id 0x4e14d8f9eb362655bb07661fd168ad429b74dfefdaf6e6c37f0fdf220a773eb5 --gas-budget 10000000
```

mint coin 只有标准coin可以使用
```bash

```


## setup
init airdrop for LUCK
```bash
sui client call --package $PKG --module airdrop --function create --type-args $PKG::luck::LUCK --args [0x7a5a0c202a1cf2e9200ca97efde
e7291b8f00e2db2a42121bf6a04b830908b1e] 120000000000000000 --gas-budget 1000000000
```

get airdrop
```bash
sui client call --package $PKG --module airdrop --function get_dorp --type-args $PKG::luck::LUCK --args 0x7b7601f380fd4e4c1b4473bc21
ad0c388a2c619198e832ab27dcbed7a5aca4c8 --gas-budget 1000000000
```


mint esLuck
```bash
sui client call --package $PKG --module esLuck --function mint --type-args $PKG::esLuck::ESLUCK --args $MINTESLUCK 10000000000000 --gas-budget 10000000
```

init airdrop for ESLUCK
```bash
sui client call --package $PKG --module airdrop --function create_non_transfer_coin --type-args $PKG::esLuck::ESLUCK --args 0x0a9992e5d5aa01f7826e043158faa79fe055f822b0781e1a2713d3962ef36e7f --gas-budget 1000000000
```

get airdrop for ESLUCK
```bash
sui client call --package $PKG --module airdrop --function get_non_trasfer_coin_dorp --type-args $PKG::esLuck::ESLUCK --args 0xfc558
95c1ff26d88b985f0465bfa514f087c5cd559ad4bd08a75124e4c9b91fa  --gas-budget 1000000000
```

mint xLuck
```bash
sui client call --package $PKG --module xLuck --function mint --type-args $PKG::xLuck::XLUCK --args $MINTXLUCK 10000000000000 --gas-budget 10000000
```

init airdrop for XLUCK
```bash
sui client call --package $PKG --module airdrop --function create_non_transfer_coin --type-args $PKG::xLuck::XLUCK --args 0x0a9992e5d5aa01f7826e043158faa79fe055f822b0781e1a2713d3962ef36e7f --gas-budget 1000000000
```

get airdrop for XLUCK
```bash
sui client call --package $PKG --module airdrop --function get_non_trasfer_coin_dorp --type-args $PKG::xLuck::XLUCK --args 0xbe656fd53e10b5552d20d8939b959b8781732405dd78cc2987258433818868a2 
--gas-budget 1000000000
```



create_pool_and_reward_esLuck
```bash
sui client call --package $PKG --module staking --function create_stake_pool --gas-budget 100000000 --type-args $PKG::esLuck::ESLUCK $PKG::sui::SUI $PKG::Luck::LUCK $PKG::xLuck::XLUCK $PKG::esLuck::ESLUCK --args $MANAGE 0x4b9bd42194bac44d9d29eb33748b02f781024e84865016a720afeea82d7b9af4 0x435071e70431492bbb8c736ccd861fb1ef08dd736867390dcb31275e6c390c20 0 0 1 168797121200 0x6
```


create_llp_pool
```bash
sui client call --package $PKG --module stake_lp --function create_stake_pool  --gas-budget 100000000 --type-args $PKG::esLuck::ESLUCK $PKG::sui::SUI $PKG::llp::LLP --args $MANAGE 0x5510a6a6d44634135a34ec8d106aa7b35d6cfc50e5f75e28277d0bead68e5eee 0x4960216c51dea999401ec3634f58ee87ebec03a5edb534d87ab3a7e3f89d4696 0 0 1 1714392749000 0x6
```


stake_luck_and_reward_esluck
```bash
sui client call --package $PKG --module staking --function stake --gas-budget 10000000 --type-args $PKG::luck::LUCK $PKG::esLuck::ES
LUCK --args $POOL [0x8f003df52f6747c231b87d966174d4e89daac7adc0a3db72202844e3c75bb814] 100000000000 0x6
```


create_vesting_pool
```bash
sui client call --package $PKG --module vesting --function create_pool --gas-budget 100000000 --type-args $PKG::esLuck::ESLUCK --args $MANAGE 86400000
```


stake for vesting
```bash
sui client call --package $PKG --module vestingNonTrasferCoin --function stake --gas-budget 100000000 --type-args $PKG::esLuck::ESLU
CK $PKG::luck::LUCK --args 0x8c3e4c3c6a8e2154c97a078adeb592fb6685a4cb42bb9c61957d3655b08d0eb7 0x317e5891f7a4879b7f924cf66f76593a4507b6
ad7f164e8ab14c1bd0de4414ab 15000000000000000 0x6
```


init vault
```bash
sui client call --package $PKG --module vault  --function create_vault --gas-budget 100000000  --type-args 0x2::sui::SUI $PKG::llp::LLP --args 0xf3012a39dca5d0f945ef2f84dfdcd14e48cf3c8d40c94dd376c31b74bf6a91e2
```

init reward xluck
```bash
sui client call --package $PKG --module xluck_reward  --function create_reward --gas-budget 100000000  --type-args $PKG::xLuck::XLUCK --args 0x1c6d9ece7878df97ccc0d6533feb38a101944385153282888ec22f19b8a0345b 100000000 1000000000
```


add liquidity
```bash
sui client call --package $PKG --module vault  --function add_liquidity  --gas-budget 100000000  --type-args 0x2::sui::SUI $PKG::llp
::LLP --args 0xda8d97f3d6644c037eb987f33257fdf00451c90d3ff6838f99639b00af16ae37 0xc25a90507180923c4290cf59ef5ac89e2e6805011ad26e323825
0930a985a591
```


play CoinFilp
```bash
sui client call --package $PKG --module coinFilp --function play --gas-budget 100000000 --type-args 0x2::sui::SUI $PKG::llp::LLP --a
rgs 0x4e3bb61e3fa89dd6b5d5eda6c4f61447300cdcb05986c21e3244f6532b8f844a [0x2c3792551e61b471bacfca22f04efec8790c916c0b7dde309a8e0ee7c5cf
41f5] 100000000 1
```


sui client call --package $PKG --module luck_vault --function deposit_luck --gas-budget 100000000 --args 0x2693d996e72841b69db80f7e637d4d320ec25fa47048157b221b3e9cbec439e0 0x59d62d661fd752a8e34e49b3a0d27c0446340d3df337c862398b84a7e438cc08

sui client call --package $PKG --module staking --function change_reward_per_sec --gas-budget 100000000 --type-args $PKG::esLuck::ESLUCK $PKG::sui::SUI $PKG::luck::LUCK $PKG::xLuck::XLUCK $PKG::esLuck::ESLUCK --args $MANAGE 0xa3fc1507401a5e435a1db5bf963a6897d6475747ad34885d23c03c4f84966c40 120000 100

## args 2023-05-1-18-00-00
### airdrop
PKG  = 0xfbfd8fc70823250ac1c6740c8e9f4442b2d66dd37828d8604a0fd7a9fb8e787b
MODULE = airdrop


#### SUI
FUNCTION = get_drop
TYPE_ARG_0 = ${PKG}::sui::SUI
ARG_0 = 0xaa6ae20a32fb813e661200ee42da3c30a50560d9f834a3c10aa75511bf429352

#### LUCK
FUNCTION = get_drop
TYPE_ARG_0 = ${PKG}::luck::LUCK
ARG_0 = 0x4de79513db23c9f8e6e900b0bb94d16379d2367d310c60fd55aec043e8b859b6


#### ESLUCK
FUNCTION = get_non_trasfer_coin_drop
TYPE_ARG_0 = ${PKG}::esLuck::ESLUCK
ARG_0 = 0x9281b570b4a8639aec89b9fc5620907e4f93ba8ded38347b0bdee0265c5b961d


#### XLUCK
FUNCTION = get_non_trasfer_coin_drop
TYPE_ARG_0 =  ${PKG}::xLuck::XLUCK
ARG_0 = 0x76bf14d8c93f8f0e1492d0eeeb35c099662ef17c3ab770387c0ef755bfc03716



### staking
PKG = 同上
MODULE = staking
ARG_0 = 0x2bd89821bfd9dce2c48c1928c715df2bb0e0545cc4d3d680283c95dccab2d8dd
VALUT = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86

#### LUCK
FUNCTION = stake_luck/stake_xluck/stake_esluck
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::luck::LUCK`,
TYPE_ARG_3 = `${pkg}::xLuck::XLUCK`,
TYPE_ARG_4 = `${pkg}::esLuck::ESLUCK`,

ARG_0 = 
ARG_1 = [COIN_OBJECT]  // type=${PKG}::luck::LUCK / ${PKG}::xLuck::XLUCK / ${PKG}::esLuck::ESLUCK
ARG_2 = COIN amount
ARG_3 = 0x6


#### unstake
FUNCTION = unstake_esluck/unstake_luck/unstake_xluck
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::luck::LUCK`,
TYPE_ARG_3 = `${pkg}::xLuck::XLUCK`,
TYPE_ARG_4 = `${pkg}::esLuck::ESLUCK`,
ARG_0 = 
ARG_1 = amount
ARG_2 = 0x6


##### CALIM
FUNCTION = claim
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::luck::LUCK`,
TYPE_ARG_3 = `${pkg}::xLuck::XLUCK`,
TYPE_ARG_4 = `${pkg}::esLuck::ESLUCK`,
ARG_0 =
ARG_1 = 0x6

### vesting ESLUCK for recrd LUCK
FUNCTION = deposit
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::luck::LUCK`,
TYPE_ARG_3 = `${pkg}::xLuck::XLUCK`,
TYPE_ARG_4 = `${pkg}::esLuck::ESLUCK`,
ARG_0 =
ARG_1 = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86
ARG_2 = [COIN_OBJECT]  // type=${PKG}::esLuck:ESLUCK
ARG_3 = COIN amount
ARG_4 = 0x6

CALIM
FUNCTION = claim_vest
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::luck::LUCK`,
TYPE_ARG_3 = `${pkg}::xLuck::XLUCK`,
TYPE_ARG_4 = `${pkg}::esLuck::ESLUCK`,
ARG_0 = 
ARG_1 = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86
ARG_2 = 0x6

FUNCTION = withdraw
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::luck::LUCK`,
TYPE_ARG_3 = `${pkg}::xLuck::XLUCK`,
TYPE_ARG_4 = `${pkg}::esLuck::ESLUCK`,
ARG_0 = 
ARG_1 = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86
ARG_2 = 0x6


#### STAKING_LP
MODULE = stake_lp
ARG_0 = 0x1d206c321475d8bd238f4bb1b75366d0a5c4dcaf14d3b50d7b2ca5169c44f266

#### stake
FUNCTION = stake
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::llp::LLP`,
ARG_0 = 
ARG_1 = [COIN_OBJECT]  // ${pkg}::llp::LLP
ARG_2 = COIN amount
ARG_3 = 0x6

#### unstake
FUNCTION = unstake
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::llp::LLP`,
ARG_0 =
ARG_1 = amount
ARG_2 = 0x6

##### CALIM
FUNCTION = claim
TYPE_ARG_0 = `${pkg}::esLuck::ESLUCK`,
TYPE_ARG_1 = `${pkg}::sui::SUI`,
TYPE_ARG_2 = `${pkg}::llp::LLP`,
ARG_0 =
ARG_1 = 0x6



### vesting XLUCK for recrd LUCK
MODULE = vesting
FUNCTION = deposit
TYPE_ARG_0 = `${PKG}::xLuck::XLUCK`
ARG_0 = 0xb14d2df00a7f18953b5e242624231734c80004c203e7ec2e660de603ebadac8d
ARG_1 = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86
ARG_2 = [COIN_OBJECT]  // type=${PKG}::xLuck::XLUCK
ARG_3 = COIN amount
ARG_4 = 0x6

CALIM
FUNCTION = claim
TYPE_ARG_0 = `${PKG}::xLuck::XLUCK`,
ARG_0 = 0xb14d2df00a7f18953b5e242624231734c80004c203e7ec2e660de603ebadac8d
ARG_1 = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86
ARG_2 = 0x6

FUNCTION = withdraw
TYPE_ARG_0 = `${PKG}::xLuck::XLUCK`,
ARG_0 = 0xb14d2df00a7f18953b5e242624231734c80004c203e7ec2e660de603ebadac8d
ARG_1 = 0x5d6cb47014fedb0878500060a42cfdbb5756a0b6a07ce972164ae006cc19ba86
ARG_2 = 0x6


### Games
#### Valut
VALUT_POOL: 0xe25c5b80af83bc9ca9796eef2c391101e3b5e939bf951ed72b9baaaf16a0dd0d
XLUCK_REWARD: 0x2e7768cc255feb8702235d242cde532949b8d60268e0865e60aa30ce20a11798
GAME_CONTROLLER: 0xef393d82b38ccc0ee3a3b8279eeed5a7bb63a6d7504fe97226b6d938c158953c

#### add_liquidity
MODULE = vault
FUNCTION = add_liquidity
TYPE_ARG_0 = ${PKG}::sui::SUI
TYPE_ARG_1 = ${PKG}::llp::LLP
ARG_0 = 
ARG_1 = COIN_OBJECT_ID  // type=${PKG}::sui::SUI

#### remove_liquidity
MODULE = vault
FUNCTION = remove_liquidity
TYPE_ARG_0 = ${PKG}::sui::SUI
TYPE_ARG_1 = ${PKG}::llp::LLP
ARG_0 = 
ARG_1 = COIN_OBJECT_ID  // type=${PKG}::llp::LLP


#### coinFilp
MODULE = coinFlip
FUNCTION = play
TYPE_ARG_0 = ${PKG}::sui::SUI
TYPE_ARG_1 = ${PKG}::llp::LLP
ARG_0 = ${VALUT_POOL}
ARG_1 = ${GAME_CONTROLLER}
ARG_2 = [COIN_OBJECT]  // type=0x2::sui::SUI
ARG_3 = COIN amount
ARG_4 = 0 or 1  // bet on head or tail
ARG_5 = 0x6

#### range
MODULE = range
FUNCTION = play
TYPE_ARG_0 = ${PKG}::sui::SUI
TYPE_ARG_1 = ${PKG}::llp::LLP
ARG_0 = ${VALUT_POOL}
ARG_1 = ${GAME_CONTROLLER}
ARG_2 = [COIN_OBJECT]  // type=0x2::sui::SUI
ARG_3 = COIN amount
ARG_4 = 5-95
ARG_5 = 0x6

#### raffle
MODULE = raffle
FUNCTION = play
TYPE_ARG_0 = ${PKG}::sui::SUI
TYPE_ARG_1 = ${PKG}::llp::LLP
ARG_0 = ${VALUT_POOL}
ARG_1 = ${GAME_CONTROLLER}
ARG_2 = [COIN_OBJECT]  // type=0x2::sui::SUI
ARG_3 = COIN amount
ARG_4 = 0 or 1  // bet on head or tail
ARG_5 = 0x6

#### wheel
MODULE = wheel
FUNCTION = play
TYPE_ARG_0 = ${PKG}::sui::SUI
TYPE_ARG_1 = ${PKG}::llp::LLP
ARG_0 = ${VALUT_POOL}
ARG_1 = ${GAME_CONTROLLER}
ARG_2 = [COIN_OBJECT]  // type=0x2::sui::SUI
ARG_3 = COIN amount
ARG_4 = 2 or 3 or 6 or 48
ARG_5 = 0x6


## Stake_NFT
MODULE = xluck_reward
FUNCTION = stake_nft
TYPE_ARG_0 = `${PKG}::xLuck::XLUCK`,
ARG_0 = 0x2e7768cc255feb8702235d242cde532949b8d60268e0865e60aa30ce20a11798
ARG_1 = NFT-OBJECTID

## Stake_NFT
MODULE = xluck_reward
FUNCTION = unstake_nft
TYPE_ARG_0 = `${PKG}::xLuck::XLUCK`,
ARG_0 = 0x2e7768cc255feb8702235d242cde532949b8d60268e0865e60aa30ce20a11798
