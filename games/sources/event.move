module games::event {
    use sui::event::emit;

    struct GamePlay has copy,drop{
        game:u64,
        player:address,
        wager:u64,
        payout:u64,
        result:u64,
        profit:u64,
        xluck:u64,
    }

    public fun EmitGamePlay(game:u64,player:address,wager:u64,payout:u64,result:u64,profit:u64,xluck:u64){
        let event = GamePlay{
            game,
            player,
            wager,
            payout,
            result,
            profit,
            xluck,
        };
        emit(event);
    }
}
