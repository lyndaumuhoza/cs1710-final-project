# cs1710finalproject

## Initial Proposal + First Attempts

Initially, we proposed modeling the card game, Uno. We thought about modeling a trace from start to end in order to look at win conditions and the different scenarios which would guarantee a win. However, when we began modeling, we ran into major performance issues, which made this idea lose its appeal. We tried using an optimizer to limit the scope of Card instances, and we even cut down on the number of players to 2 and the nubmer of cards to 20, but running just a simple trace would take a long time. Therefore, we realized that we couldn't model a full trace, and needed to focus more on the properties of transitions, but given how much we cut down the model, we did not have many concrete properties we were interested in investigating.

## New Model: Towers of Hanoi

We changed our project idea to the Towers of Hanoi. This is a puzzle in which there are multiple pegs/towers, and a stack of various sized rings on one tower. The goal is to get all rings to a different tower, moving one ring at a time and ensuring that a larger ring is never placed on top of a smaller ring.

In addition, we wanted to explore several variations of this puzzle and see how they compared. The variations are \***\*\_\*\***. We chose this idea because we were introduced to this puzzle to learn recursion for the first time, so we thought it would be interesting to explore other properties that it may be useful in demonstrating.

### <Model 2 Section>

Bicolor towers

### <Model 3 Section>

Magnetic towers 

## Goals

The main goal is to see if there is correspondence between the variations of the puzzle. In other words, given a trace that satisfies the constraints of one puzzle, would it satisfy the constraints for the other?

Some other questions/properties we looked at:

- What is the minimum number of moves required to satisfy each puzzle?
- If we increase or decrease the number of rings and towers, does the minimum number of moves change?
- Is there a methodical way of approaching the puzzle? Is there a set of rules/move constraints that work for all variations of the puzzle?
- Are there constraints that make the puzzle impossible to solve?

## Design Choices and Tradeoffs

## Overview of Sigs and Predicates

## Testing


## Assumptions and Limitations

- Trace length / performance costs: \
  Since it has been mathematically proven that the minimum number of moves for the standard Towers of Hanoi puzzle is 2^n - 1, (where n is the number of rings) we could not experiment with very high numbers of rings, as the trace length would grow exponentially and the performance costs would be too high.

## Tool Choices and Justification

- Temporal forge: \
  Although we considered basic forge for this model, we ended up choosing temporal because it offers the option to limit trace length, which is especially helpful when considering that we generally know how long a trace should be. We also liked that it allows us to compare the traces at every step in time (so that there is no need to keep a separate State sig).

- Visualizer?

## Stakeholders

- Programmers / Mathematicians: Since the Towers of Hanoi is a puzzle used primarily to demonstrate recursion and induction, this model could be useful for beginner programmers and mathematicians (who might want a visual representation without having to physically make the model)
- Puzzle Players: Peeopl who are generally interested in puzzles may be interested because they can look at how the model solves the the puzzle, and compare different versions of the puzzle using this model

## Takeaways
