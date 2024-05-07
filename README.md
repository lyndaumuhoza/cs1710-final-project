# cs1710finalproject

## Initial Proposal + First Attempts

Initially, we proposed modeling the card game, Uno. We thought about modeling a trace from start to end in order to look at win conditions and the different scenarios which would guarantee a win. However, when we began modeling, we ran into major performance issues, which made this idea lose its appeal. We tried using an optimizer to limit the scope of Card instances, and we even cut down on the number of players to 2 and the nubmer of cards to 20, but running just a simple trace would take a long time. Therefore, we realized that we couldn't model a full trace, and needed to focus more on the properties of transitions, but given how much we cut down the model, we did not have many concrete properties we were interested in investigating.

## New Model: Towers of Hanoi

We changed our project idea to the Towers of Hanoi. This is a puzzle in which there are multiple pegs/towers, and a stack of various sized rings on one tower. The goal is to get all rings to a different tower, moving one ring at a time and ensuring that a larger ring is never placed on top of a smaller ring.

In addition, we wanted to explore several variations of this puzzle and see how they compared. The variations are colored towers and magnetic towers. We chose this idea because we were introduced to this puzzle to learn recursion for the first time, so we thought it would be interesting to explore other properties that it may be useful in demonstrating.

### Bicolor towers

In this variation of the Towers of Hanoi, each ring has one of two colors. The initial tower starts with the rings alternating in color. The goal is to get all rings to another tower without allowing two rings of the same color to be stacked. The basic size contstraint of the original puzzle applies here as well.

### Magnetic towers

In this variation of the Towers of Hanoi, each ring has magnetic poles, with either the North side facing up or the South side facing up. The initial tower starts with all rings facing in the same direction. Everytime a ring is moved, the ring must be flipped. The goal is to get all the rings to another tower without allowing two rings to have the same pole facing each other (as this would prepel the rings). The basic size constraint still applies here as well.

## How to Interpret Our Model

## Goals

The main goal is to see if there is correspondence between the variations of the puzzle. In other words, given a trace that satisfies the constraints of one puzzle, would it satisfy the constraints for the other?

Some other questions/properties we looked at:

- What is the minimum number of moves required to satisfy each puzzle?
- If we increase or decrease the number of rings and towers, does the minimum number of moves change?
- Is there a methodical way of approaching the puzzle? Is there a set of rules/move constraints that work for all variations of the puzzle?
- Are there constraints that make the puzzle impossible to solve?

## Design Choices and Tradeoffs

## Overview of Sigs and Predicates

Although we worked with a lot of model variations, the main Sigs are for Ring and Tower, and the baisc predicates are init, move, wellformed, and endState, which are all needed to run a successful trace from start to end. 

In the basic model, Ring has the below field to keep track of which ring it is stacked on. Tower has a top field to keep track of the top ring in its stack. In the magnetic variation, Ring has a polarity field to keep track of which pols is faced up, and Tower also has a polarity field which restrics which state of rings can be stacked on it. In the colored variation, Ring has an additional color property but Tower stays the same as the basic model.

Init specifies the state of the starting tower. Wellformed ensures that no rings are stacked on smaller rings (along with other constraints for the other variations). Move specifies the action of moving one ring, and ensuring all other rings remain in place. End state specifies the state of the ending tower. 

## Challenges

Tracking the trace lengths using a counter was difficult, we were running into an issue where our counter can increment or decrement by any number other than 1. Solution: 

## Testing

### Current Testing Plan
- Test that min trace length for basic towers = 7, but is satisfiable in more steps (using counter)
- Test that min trace length for magnetic towers = 13, but is satisfiable in more steps (using counter)
- Test that min trace length for colored towers = 7, but is satisfiable in more steps (using counter)
- Test that changing the number of towers to 2 makes the puzzle unsat for all three variations
- Test that changing the number of towers to 4 decreases the minimum trace length for all three variations
- Test to see if there is correspondence between the magnetic variation and the two colors (if given a trace that satisfies the magnetic constraints, will it always satisfy the colored version?)
- Verify that both magnetic and colored variations correspond to basic version (expected, bc they are just extensions of original puzzle)
- Verify that no disk will ever be placed on a disk smaller than it
- Verify that in magnetic variation, all disks in a tower will have same polarity 
- Verify that in colored variation, no two disks of the same color are placed on each other
- Verify that init and endstate are equivalent for all variations
- For each puzzle, verify the expected trace length for two disks + three towers, four disks + three towers (if not too long), etc
- Verify that colored variation is unsat with four disks + three towers
- Verify wellformed using induction
- Basic unit testing for predicates


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
