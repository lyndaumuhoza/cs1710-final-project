#lang forge/temporal

// Start with 2 players
// Cards: (6 number cards +3 special cards per color + 2 wild types) x 4 = 44

abstract sig Player sig {
    cards set
    }
Player1 extends player, Player 2 
Card sig - color
number card extend card, and add number
Special cards extend card, and add symbol
sig Game {
    turn: var Player
    last_card: var Card
}
sig Deck { // python script
    set: Card
}

Rules:
Predicates for rules:
pred for matching previous number or color: (game.last_card.number = game.last_card.number' or game.last_card.color = game.last_card.color')
pred for special cards: (if (game.last_card = Skip or game.last_card = Reverse) implies game.turn = game.turn' or 
                        if game.last_card = +2 implies draw(game.turn) or 
                        if game.last_card = wild implies game.last_card.color != game.last_card.color')


pred draw(player): if game.last_card = +2 implies game.turn.cards' = game.turn.cards + some Card in Deck and game.turn' = game.turn
                   if game.last_card = +4 implies game.turn.cards' = game.turn.cards + some Card in Deck and game.turn' = game.turn
                   
pred noMatch:
    if (no special_card: SpecialCard | special_card in  game.turn.cards and special_card.color = game.last_card.color or special_card.color=black) and (no c: Card | c in game.turn.cards and (c.color = game.last_card.color or c.number = game.last_card.number)) implies {
        game.turn.cards' = game.turn.cards + some Card in Deck and game.turn' = game.turn
    }

pred winStrategy(LoosingPlayer): 
    // guaranteed loose/win
    no c: Card | c in LoosingPlayer.cards and (c = skip or c = reverse or c = +2  or c = +4)


Win condition: If a player runs out cards after their turn, they win, and game ends



General rules:
Starting player can play any card, succeeding players should match the previous number or color.


If a player plays a skip card, the next player doesn’t play. The skip card must match the previous player’s card number or color.
If a player plays a reverse card, the previous player has to play again. The reverse card must match the previous player’s card number or color.
If a player plays +2 card, the next player has to draw two cards, and doesn’t play. The +2 card must match the previous player’s card number or color.
If a player plays +4 card, the next player has to draw four cards. This can be played at any point in the game
If a player plays the wild card, they get to choose the color they want the next cards to be. This can also be played at any point in the game.
