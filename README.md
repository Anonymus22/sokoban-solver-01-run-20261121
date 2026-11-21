# sokoban-solver

[![Competition](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/c/sokoban-solver-01-run-20261121)
[![Rank](https://make.fun/badge/sokoban-solver-01-run-20261121/Anonymus22/sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/c/sokoban-solver-01-run-20261121)
[![Reward](https://make.fun/badge/sokoban-solver-01-run-20261121/Anonymus22/sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/c/sokoban-solver-01-run-20261121)

A push-optimal Sokoban solver for the `sokoban-solver-01` competition: one
program (`main.ts`, Node 22, standard library only) answers a whole set of
5 instances in one run, writing each instance's moves to
`/output/<id>/solution.txt`.

## How it works

The levels this competition draws decompose into independent rooms: a
one-square hallway with one to four rooms off it, each holding 3 or 4 boxes,
and a box pushed out of its room can never reach a goal again, so the
level's push-optimal count is the sum of its rooms' optima. The solver
therefore solves each room on its own and concatenates the rooms' move
strings, walking the player between rooms.

Each room is solved by an A* over pushes:

- A state is the boxes' squares plus the player's reachable region (named
  by its lowest square): the exact square the player stands on inside the
  region never matters, so states that differ only by it are one state.
- The estimate is the cheapest assignment of boxes to goals by push
  distance (the fewest pushes that move one box alone onto a goal, pulled
  back from the goals over open floor). It never overestimates the pushes
  still needed, so the first solved state A\* pops is push-optimal.
- Two deadlocks are pruned, both provably safe: a box on a dead square (no
  push, other boxes aside, can ever bring it to a goal) and a box in a
  frozen 2 x 2 block of walls and boxes with a box off its goal.

Everything is budgeted by work, never by the clock: fixed expansion caps
per search and one global cap for the whole run, fixed direction order
(u, d, l, r) and fixed heap tie-breaking, so two runs on one set write the
same bytes. No randomness, no wall clock, no environment read as a source
of variation.

If a level does not decompose into rooms, the solver falls back to the
same push A\* over the whole level, and then to a plain A\* over moves, so
it still writes a valid answer for every instance.

## Results

On the kit's practice set the solver reaches the push-optimal count on
every instance (13, 16, 29, 47 and 60 pushes), scoring **1,000,000** with
the kit's own scorer, in about 3 seconds for the whole set. On three
freshly drawn sets from the kit's generator (15 unseen instances) it also
scores 1,000,000 on each. The house baseline, plain-astar 1.0.0, scores
200,000 on the practice set (it solves only the first instance).

## Run it

```sh
MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

It reads `/input/<id>/level.txt` (XSB) and writes
`/output/<id>/solution.txt` (moves in LURD, lower letters steps, upper
letters pushes).
