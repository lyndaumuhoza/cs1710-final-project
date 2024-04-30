#lang forge/temporal

open "uno.frg"

pred cardMatch {
    {Game.last_card.color = Game.last_card'.color or Game.last_card.symbol = Game.last_card'.symbol}
}
test suite for playCard {
    assert cardMatch is necessary for playCard for 20 Card, 2 Player for optimizer
    test expect {
        // cardMatchTrue: {cardMatch and playCard} is theorem for 20 Card, 2 Player for optimizer
    }
}