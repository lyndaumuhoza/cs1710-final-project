#lang forge/temporal

// Start with 2 players
// Cards: (6 symbol cards +3 special cards per color + 2 wild types) x 4 = 44

option max_tracelength 13
option min_tracelength 12

abstract sig Color {}
one sig Blue, Green, Black extends Color {}

sig Card {
    color: one Color,
    symbol: one Int
}

abstract sig Player {
    var cards: set Card
}
one sig Player1, Player2 extends Player {}
one sig Winner {
    winner: one Player
}


inst optimizer {
    Card = `ZeroBlue + `OneBlue + `TwoBlue + `ThreeBlue + `FourBlue + `FiveBlue + `SkipBlue + `ReverseBlue + `PlusTwoBlue + 
    `ZeroGreen + `OneGreen + `TwoGreen + `ThreeGreen + `FourGreen + `FiveGreen + `SkipGreen + `ReverseGreen + `PlusTwoGreen + 
    `WildCard + `PlusFour

    Blue = `Blue
    Green = `Green
    Black = `Black
    Color = `Blue + `Green + Black

    color = `ZeroBlue -> `Blue + `OneBlue -> `Blue + `TwoBlue -> `Blue + `ThreeBlue -> `Blue + `FourBlue -> `Blue + `FiveBlue -> `Blue + `SkipBlue -> `Blue + `ReverseBlue -> `Blue + `PlusTwoBlue -> `Blue + 
    `ZeroGreen -> `Green + `OneGreen -> `Green + `TwoGreen -> `Green + `ThreeGreen -> `Green + `FourGreen -> `Green + `FiveGreen -> `Green + `SkipGreen -> `Green + `ReverseGreen -> `Green + `PlusTwoGreen-> `Green + 
    `PlusFour -> `Black + `WildCard -> `Black

    symbol = `ZeroBlue -> 0 + `OneBlue -> 1 + `TwoBlue -> 1 + `ThreeBlue -> 3 + `FourBlue -> 4 + `FiveBlue -> 5 + `SkipBlue -> -1 + `ReverseBlue -> -3 + `PlusTwoBlue -> -2 + 
    `ZeroGreen -> 0 + `OneGreen -> 1 + `TwoGreen -> 1 + `ThreeGreen -> 3 + `FourGreen -> 4 + `FiveGreen -> 5 + `SkipGreen -> -1 + `ReverseGreen  -> -3 + `PlusTwoGreen-> -2 + 
    `PlusFour -> -4 + `WildCard -> -5
}


// symbol card extend card, and add symbol
// Special cards extend card, and add symbol
one sig Game {
    var turn: one Player,
    var last_card: one Card
}
// one sig Deck { 
//     var all_cards: set Card
// }

pred init {
    // start with player 1 already putting something down, so it's player 2's turn

    Game.turn = Player2
    #{Player1.cards} = 4
    #{Player2.cards} = 5
    // #{Deck.all_cards} = 11
}

pred wellformed {
    // no overlap between hands / deck
    #{Player1.cards & Player2.cards} = 0
    Game.last_card not in Player1.cards
    Game.last_card not in Player2.cards
    // #{Player2.cards & Deck.all_cards} = 0
    // #{Player1.cards & Deck.all_cards} = 0
}

// Rules:
// Predicates for rules:
pred playCard {
    // Game.last_card'.symbol = Game.last_card.symbol or Game.last_card'.color = Game.last_card.color or Game.last_card'.symbol = -4 or Game.last_card'.symbol = -5
    some p: Player, c: Card | {
        c in p.cards
        Game.turn = p
        p.cards' = p.cards - c
        Game.last_card' = c
        c.color = Game.last_card.color or c.symbol = Game.last_card.symbol or c.symbol = -4 or c.symbol = -5
    }
    Game.turn = Player2 implies Player1.cards = Player1.cards'
    Game.turn = Player1 implies Player2.cards = Player2.cards'
    // Deck.all_cards' = Deck.all_cards
    // Game.turn' != Game.turn
    (Game.turn = Player2) implies (Game.turn' = Player1)
    (Game.turn = Player1) implies (Game.turn' = Player2)

}

pred specialCardRules {
    // ((game.last_card = Skip or game.last_card = Reverse) implies game.turn = game.turn' or 
    // if game.last_card = +2 implies draw(game.turn) or 
    // if game.last_card = wild implies game.last_card.color != game.last_card.color')
    (Game.last_card.symbol = -1 or Game.last_card.symbol = -3) implies Game.turn = Game.turn'
    (Game.last_card.symbol = -2) implies drawCardNoPlay
    (Game.last_card.symbol = -5 or Game.last_card.symbol = -4) implies Game.last_card.color != Game.last_card'.color
    (Game.last_card.symbol = -4) implies drawCardNoPlay
}

pred noMatchMustDraw {
    no c: Card | c in Game.turn.cards and (c.color = Game.last_card.color or c.symbol = Game.last_card.symbol)
}

pred drawCardPlay {
    noMatchMustDraw 

    some c: Card | {
        c in Deck.all_cards
        Deck.all_cards' = Deck.all_cards - c
        (Game.last_card.symbol = c.symbol or Game.last_card.color = c.color) => Game.last_card' = c else {Game.turn.cards' = Game.turn.cards + c}
        Game.turn' != Game.turn
        all other: Player | other != Game.turn implies other.cards = other.cards'
    }
}
pred drawCardNoPlay {
    // if game.last_card = +2 implies game.turn.cards' = game.turn.cards + some Card in Deck and game.turn' = game.turn
    // f game.last_card = +4 implies game.turn.cards' = game.turn.cards + some Card in Deck and game.turn' = game.turn
    Game.last_card.symbol = -2  implies {
        some disj c1, c2: Card | {
            c1 in Deck.all_cards and c2 in Deck.all_cards
            Game.turn.cards' = Game.turn.cards + c1 + c2
            Deck.all_cards' = Deck.all_cards - c1 - c2
        }
    }
    Game.last_card.symbol = -4 implies {
        some disj c1, c2, c3, c4: Card | {
            c1 in Deck.all_cards and c2 in Deck.all_cards and c3 in Deck.all_cards and c4 in Deck.all_cards
            Game.turn.cards' = Game.turn.cards + c1 + c2 + c3 + c4
            Deck.all_cards' = Deck.all_cards - c1 - c2 - c3 - c4       
        }
    }
    // all other players keep their cards
    Game.last_card = Game.last_card'
    Game.turn = Player2 implies Player1.cards = Player1.cards'
    Game.turn = Player1 implies Player2.cards = Player2.cards'
    Game.turn' != Game.turn
}

pred winScenario {
    ((#{Player1.cards} = 0) and Winner.winner = Player1) or ((#{Player2.cards} = 0) and Winner.winner = Player2)
}

pred trace {
    init
    always wellformed
    always {drawCardPlay or drawCardNoPlay or playCard}
    always specialCardRules
    eventually winScenario
}

run {init and always(playCard) and eventually winScenario} for exactly 20 Card, 2 Player for optimizer
                   

// pred winStrategy(LoosingPlayer): 
//     // guaranteed loose/win
//     no c: Card | c in LoosingPlayer.cards and (c = skip or c = reverse or c = +2  or c = +4)


// Win condition: If a player runs out cards after their turn, they win, and game ends


// General rules:
// Starting player can play any card, succeeding players should match the previous symbol or color.


// If a player plays a skip card, the next player doesn’t play. The skip card must match the previous player’s card symbol or color.
// If a player plays a reverse card, the previous player has to play again. The reverse card must match the previous player’s card symbol or color.
// If a player plays +2 card, the next player has to draw two cards, and doesn’t play. The +2 card must match the previous player’s card symbol or color.
// If a player plays +4 card, the next player has to draw four cards. This can be played at any point in the game
// If a player plays the wild card, they get to choose the color they want the next cards to be. This can also be played at any point in the game.
