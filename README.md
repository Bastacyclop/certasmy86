## certasmy86
### Goal
This is a formally verified y86 encoder/decoder, the specification of which can
be found here: [http://tinyurl.com/y7x46wf7](http://tinyurl.com/y7x46wf7).

### Architecture
Filenames are quite eponymous:
- ast.v: Contains everything related to the ast, see figure 4.2 of the
  specification.
- stream.v: Defines streams, and a few proofs about them.
- encode.v: Takes care of encoding data into a stream. 
- decode.v: Takes care of decoding data from a stream.
- bijection.v: Proofs that you can go back and forth between encoding and
  decoding.
- util.v: Contains various tactics.

### Interesting points
We represent a stream of bits with a list of booleans. For performance reasons,
encoding and decoding operations always return the stream they operated on in
order to simulate mutability. For example, the `decode.number` function decodes
a number encoded on N bits from a stream and returns an option containing
the number and the stream without its first N bits.

Because of this decision, Coq wasn't able to generate a termination proof for
our decoding functions. A possible solution would have been to give "fuel" to
our main function, which would have helped Coq know how to generate a
termination proof. Instead of doing that, we decided to write the termination
proof ourselves.

Another performance decision was the use of N. This was necessary because
before proving our functions correct, we decided to test them in order to make
sure we were proving the right thing. Coq's `nat` type is pretty slow and
overflows the stack when it comes to manipulating large numbers, hence the use
of N.

One of the problems that arises when using N is that the Omega tactic doesn't
know how to solve equations on N. Because of that, we had to `admit` a few
proofs, often when what we tried to prove was quite obvious.
