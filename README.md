This is an attempt to formalize some minimal aspects of differential geometry. In the process I hope to solidify and deepen my understanding of the subject and related topics I've learned this year. It is also my 3rd iteration of formalizing differentiability.

I am not aiming to write the best, most general version of definitions and theorems the first time, but rather write manageable chunks and generalize only when it makes things easier to do. I am also focusing on **ergonomics** (again, when it's easy to do so). This means adding coercions and instances liberally so things that should work just work.

I'm also aiming for **practicality**. I refrain from using unfamiliar concepts as much as possible, so the library can reach the widest audience. In particular this means I am not formalizing things like synthetic differential geometry, clifford algebra, or differential forms (at least not yet). I also don't currently have a deep enough knowledge to formalize any of those things. One note of contention may be the use of the Caratheodory derivative over the Frechet (although there will be an equivalence proof). I believe this choice is justified, especially from a software engineering perspective, since it turns many epsilon-delta proofs into continuity proofs, which avoids repeated work and leaky abstractions. Other reasons for this choice are outlined in the README.md within `src`.

My work builds off Patrick Massot's attempts. (See https://github.com/PatrickMassot/lean-differential-topology) In the future our attempts may coalesce, but for now they are separate. Once I am confident I can work on this project steadily for a decent amount of time and I have formalized a decent amount I will work to combine the efforts. Working separately gives me more freedom to see if my ideas pan out and to dramatically reorganize Patrick's existing work.

In order to begin to formalize differential geometry, several intermediate structures are necessary. The following are just some of the concepts that must be formalized before we can get to more complicated topics.

## Topology
There is a lot of existing topology formalism, however there are several import pieces missing:
- pointwise continuity
- homeomorphisms
- homotopy (postponed)

## Normed Vector Spaces
- operator norm

Patrick has done a great job with this. I am slightly tweaking it and still unsure about whether the relationship between norms and metrics is the correct one.

## Differentiability
- derivatives
- diffeomorphisms
- differential operators (maybe?)

Coquelicot is probably the most sophisticated existing library for real analysis. I intend to build higher rather than flesh out analysis results for now.

## Manifolds
- topological manifolds
- smooth manifolds

Doing this properly will require piecing through some of the ambiguity around what goes into a chart. Is it really a pair? If it isn't, can it be treated as one?

## Linear Algebra (Sort Of)
- continuous linear maps / bounded linear operators
- multilinear maps
- tensors

https://ncatlab.org/nlab/show/continuous+multilinear+operator