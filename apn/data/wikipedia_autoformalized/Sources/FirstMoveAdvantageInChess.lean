/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# First-move advantage in chess

What is the outcome of a perfectly played game of chess?

Chess is a finite two-player zero-sum game of perfect information, so by Zermelo's theorem
exactly one of the following holds: White can force a win, Black can force a win, or both
players can force at least a draw. Which one holds is not known. The consensus among players
and theorists (Steinitz, Lasker, Capablanca, Fischer, Kasparov, ...) is that chess is a draw
with best play; a minority view (Adams, Berliner) is that White can force a win.

No model of chess exists in Mathlib, so this file formalises the FIDE Laws of Chess from
scratch:

* `Board`, `Position`, `Move`: the pieces on the 64 squares, the side to move, castling rights
  and the en passant square; a move is given by its source and destination squares together
  with an optional promotion piece (castling is the two-square king move, en passant is the
  diagonal pawn move onto the en passant square).
* `Position.IsLegal`: the legal moves (FIDE Article 3), including castling, en passant,
  promotion and the rule that a move may not leave one's own king in check.
* `GameState.result`: the game ends with checkmate (Art. 5.1.1), stalemate (Art. 5.2.1),
  fivefold repetition (Art. 9.6.1) or the 75-move rule (Art. 9.6.2).
* `GameState.CanClaimDraw`: the player to move may claim a draw by threefold repetition
  (Art. 9.2) or by the 50-move rule (Art. 9.3), also with an intended move.
* `CanForceWin c s`: player `c` has a strategy from the state `s` that wins against every
  defence; a defender who can claim a draw is assumed to do so.
* `perfectPlayOutcome`: the game-theoretic value of chess from the standard initial position.

The following rules are omitted because they cannot change the game-theoretic value: draw by
agreement (Art. 9.1), resignation (Art. 5.1.2) and the dead position rule (Art. 5.2.2); from a
dead position no play can end in checkmate, so every continuation is drawn anyway. Rules about
clocks, arbiters and irregularities are not part of the mathematical game.

The 75-move rule makes the game finite: a game contains at most $96$ pawn moves and $30$
captures, and at most $150$ consecutive half-moves without either, so every game ends after a
bounded number of half-moves. Hence Zermelo's theorem applies and `perfectPlayOutcome` is a
draw if and only if neither player can force a win.

*References:*
- [Wikipedia: First-move advantage in chess](https://en.wikipedia.org/wiki/first-move_advantage_in_chess)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia: Solving chess](https://en.wikipedia.org/wiki/Solving_chess)
- [FIDE Laws of Chess](https://handbook.fide.com/chapter/E012023)
- C. E. Shannon, *Programming a Computer for Playing Chess*, Philosophical Magazine 41 (1950),
  256–275.
-/

namespace FirstMoveAdvantageInChess

/- ### Pieces and squares -/

/-- The two players. White moves first. -/
inductive Color
  | white
  | black
  deriving DecidableEq, Fintype

/-- The opponent of a player. -/
def Color.other : Color → Color
  | .white => .black
  | .black => .white

/-- The rank increment of a forward pawn move of colour `c`. -/
def Color.forward : Color → ℤ
  | .white => 1
  | .black => -1

/-- The rank on which the pieces of colour `c` start. Ranks 1–8 are numbered `0`–`7`. -/
def Color.homeRank : Color → Fin 8
  | .white => 0
  | .black => 7

/-- The rank on which the pawns of colour `c` start. -/
def Color.pawnRank : Color → Fin 8
  | .white => 1
  | .black => 6

/-- The rank on which the pawns of colour `c` promote. -/
def Color.lastRank : Color → Fin 8
  | .white => 7
  | .black => 0

/-- The six kinds of pieces. -/
inductive PieceType
  | king
  | queen
  | rook
  | bishop
  | knight
  | pawn
  deriving DecidableEq, Fintype

/-- A piece: a colour and a kind. -/
structure Piece where
  color : Color
  type : PieceType
  deriving DecidableEq, Fintype

/-- A square of the board. Files a–h and ranks 1–8 are both numbered `0`–`7`; for example
`⟨4, 0⟩` is the square e1. -/
structure Square where
  file : Fin 8
  rank : Fin 8
  deriving DecidableEq, Fintype

namespace Square

/-- The file difference from `s` to `t`. -/
def dx (s t : Square) : ℤ := (t.file : ℤ) - s.file

/-- The rank difference from `s` to `t`. -/
def dy (s t : Square) : ℤ := (t.rank : ℤ) - s.rank

/-- The Chebyshev (king-move) distance between two squares. -/
def dist (s t : Square) : ℤ := max |s.dx t| |s.dy t|

/-- `s` and `t` are distinct squares on a common rank or file. -/
def OnRookLine (s t : Square) : Prop := s ≠ t ∧ (s.dx t = 0 ∨ s.dy t = 0)

/-- `s` and `t` are distinct squares on a common diagonal. -/
def OnBishopLine (s t : Square) : Prop := s ≠ t ∧ |s.dx t| = |s.dy t|

/-- `s` and `t` are distinct squares on a common rank, file or diagonal. -/
def OnLine (s t : Square) : Prop := s.OnRookLine t ∨ s.OnBishopLine t

/-- `u` lies strictly between `s` and `t` on a common rank, file or diagonal. -/
def StrictlyBetween (s t u : Square) : Prop :=
  s.OnLine t ∧ s.OnLine u ∧ (s.dx t).sign = (s.dx u).sign ∧ (s.dy t).sign = (s.dy u).sign ∧
    s.dist u < s.dist t

instance (s t : Square) : Decidable (s.OnRookLine t) := by unfold OnRookLine; infer_instance
instance (s t : Square) : Decidable (s.OnBishopLine t) := by unfold OnBishopLine; infer_instance
instance (s t : Square) : Decidable (s.OnLine t) := by unfold OnLine; infer_instance
instance (s t u : Square) : Decidable (s.StrictlyBetween t u) := by
  unfold StrictlyBetween; infer_instance

end Square

/-- The number halfway between `a` and `b`. It is the file of the rook's destination when
castling and the rank of the en passant square after a two-square pawn move. -/
def midpoint (a b : Fin 8) : Fin 8 := ⟨(a.val + b.val) / 2, by omega⟩

/-- The squares `t` that a piece of kind `pt` standing on `s` could move to on an otherwise
empty board (FIDE Art. 3.2–3.6). Pawns are treated separately. -/
def PieceType.Pattern : PieceType → Square → Square → Prop
  | .king, s, t => s.dist t = 1
  | .queen, s, t => s.OnLine t
  | .rook, s, t => s.OnRookLine t
  | .bishop, s, t => s.OnBishopLine t
  | .knight, s, t => |s.dx t| * |s.dy t| = 2
  | .pawn, _, _ => False

instance (pt : PieceType) (s t : Square) : Decidable (pt.Pattern s t) := by
  cases pt <;> unfold PieceType.Pattern <;> infer_instance

/-- The squares `t` on which the piece `pc` standing on `s` could capture, ignoring the other
pieces on the board. A pawn captures one square diagonally forward (Art. 3.7.3). -/
def Piece.AttackPattern (pc : Piece) (s t : Square) : Prop :=
  if pc.type = .pawn then s.dy t = pc.color.forward ∧ |s.dx t| = 1 else pc.type.Pattern s t

instance (pc : Piece) (s t : Square) : Decidable (pc.AttackPattern s t) := by
  unfold Piece.AttackPattern; infer_instance

/- ### Boards -/

/-- A board assigns to every square the piece standing on it, if any. -/
abbrev Board := Square → Option Piece

namespace Board

/-- No piece stands strictly between the squares `s` and `t`. -/
def PathClear (b : Board) (s t : Square) : Prop := ∀ u, s.StrictlyBetween t u → b u = none

/-- Some piece of colour `c` attacks the square `t` (Art. 3.1): it could capture on `t`, even if
it is pinned (Art. 3.1.3). -/
def Attacks (b : Board) (c : Color) (t : Square) : Prop :=
  ∃ s pc, b s = some pc ∧ pc.color = c ∧ pc.AttackPattern s t ∧ b.PathClear s t

/-- The king of colour `c` is attacked by the opponent (Art. 3.9.1). -/
def InCheck (b : Board) (c : Color) : Prop :=
  ∃ k, b k = some ⟨c, .king⟩ ∧ b.Attacks c.other k

instance (b : Board) (s t : Square) : Decidable (b.PathClear s t) := by
  unfold PathClear; infer_instance
instance (b : Board) (c : Color) (t : Square) : Decidable (b.Attacks c t) := by
  unfold Attacks; infer_instance
instance (b : Board) (c : Color) : Decidable (b.InCheck c) := by unfold InCheck; infer_instance

end Board

/- ### Positions and moves -/

/-- The two wings on which a king may castle. -/
inductive Wing
  | kingside
  | queenside
  deriving DecidableEq, Fintype

/-- The initial square of the king of colour `c`. -/
def Color.kingSquare (c : Color) : Square := ⟨4, c.homeRank⟩

/-- The initial square of the rook of colour `c` on wing `w`. -/
def Color.rookSquare (c : Color) : Wing → Square
  | .kingside => ⟨7, c.homeRank⟩
  | .queenside => ⟨0, c.homeRank⟩

/-- The square on which the king of colour `c` lands when castling on wing `w`. -/
def Color.castleSquare (c : Color) : Wing → Square
  | .kingside => ⟨6, c.homeRank⟩
  | .queenside => ⟨2, c.homeRank⟩

/-- A chess position: the pieces on the board, the side to move, the castling rights and the
en passant square. -/
structure Position where
  /-- The pieces on the board. -/
  board : Board
  /-- The player who has the move. -/
  toMove : Color
  /-- `castling c w` holds when neither the king of colour `c` nor its rook on wing `w` has
  moved yet, and this rook has not been captured (Art. 3.8.2.1). -/
  castling : Color → Wing → Bool
  /-- The square passed over by a pawn that has just advanced two squares, if any
  (Art. 3.7.3.1). -/
  enPassant : Option Square
  deriving DecidableEq

/-- A move: the square the moving piece leaves, the square it lands on, and the piece a pawn
promotes to (for promotions only). Castling is recorded as the two-square move of the king, and
an en passant capture as the diagonal move of the capturing pawn onto the en passant square. -/
structure Move where
  src : Square
  dst : Square
  promotion : Option PieceType
  deriving DecidableEq, Fintype

namespace Position

/-- The position obtained by playing the move `m` (the result is only meaningful when
`p.IsLegal m`). The moving piece leaves `m.src` and lands on `m.dst`, replaced by the promotion
piece if any; an en passant capture removes the captured pawn; castling also moves the rook to
the square the king passed over. Castling rights are lost by moving the king, by moving a rook
from its initial square and when a rook is captured on its initial square. -/
def play (p : Position) (m : Move) : Position :=
  match p.board m.src with
  | none => p
  | some pc =>
    let placed : Piece := match m.promotion with
      | some q => ⟨pc.color, q⟩
      | none => pc
    let b₁ : Board := Function.update (Function.update p.board m.src none) m.dst (some placed)
    let b₂ : Board :=
      if pc.type = .pawn ∧ p.enPassant = some m.dst then
        Function.update b₁ ⟨m.dst.file, m.src.rank⟩ none
      else b₁
    let b₃ : Board :=
      if pc.type = .king ∧ |m.src.dx m.dst| = 2 then
        Function.update
          (Function.update b₂ ⟨if m.src.file < m.dst.file then 7 else 0, m.src.rank⟩ none)
          ⟨midpoint m.src.file m.dst.file, m.src.rank⟩ (some ⟨pc.color, .rook⟩)
      else b₂
    { board := b₃
      toMove := pc.color.other
      castling := fun c w => p.castling c w &&
        decide (m.src ≠ c.kingSquare ∧ m.src ≠ c.rookSquare w ∧ m.dst ≠ c.rookSquare w)
      enPassant :=
        if pc.type = .pawn ∧ |m.src.dy m.dst| = 2 then
          some ⟨m.src.file, midpoint m.src.rank m.dst.rank⟩
        else none }

/-- The move `m` of a pawn of the side to move is a pawn move (Art. 3.7): one square forward to
an empty square; two squares forward from the pawn's initial rank over an empty square to an
empty square; or one square diagonally forward, capturing a piece there or capturing en passant.
A pawn reaching the last rank must promote to a queen, rook, bishop or knight. -/
def PawnMove (p : Position) (m : Move) : Prop :=
  ((m.src.dx m.dst = 0 ∧ p.board m.dst = none ∧
      (m.src.dy m.dst = p.toMove.forward ∨
        (m.src.dy m.dst = 2 * p.toMove.forward ∧ m.src.rank = p.toMove.pawnRank ∧
          p.board.PathClear m.src m.dst))) ∨
    (|m.src.dx m.dst| = 1 ∧ m.src.dy m.dst = p.toMove.forward ∧
      (p.board m.dst ≠ none ∨ p.enPassant = some m.dst))) ∧
  (m.promotion = none ↔ m.dst.rank ≠ p.toMove.lastRank) ∧
  ∀ q, m.promotion = some q → q ≠ .king ∧ q ≠ .pawn

/-- The move `m` is a castling move of the side to move (Art. 3.8.2): the king moves from its
initial square two squares towards a rook of the same colour on its initial square, neither of
which has moved (the castling right is intact); all squares between the king and the rook are
empty; and the king does not stand on, pass over or land on a square attacked by the opponent.
-/
def Castles (p : Position) (m : Move) : Prop :=
  ∃ w, m.src = p.toMove.kingSquare ∧ m.dst = p.toMove.castleSquare w ∧
    p.castling p.toMove w = true ∧
    p.board (p.toMove.rookSquare w) = some ⟨p.toMove, .rook⟩ ∧
    p.board.PathClear m.src (p.toMove.rookSquare w) ∧
    ∀ u, u = m.src ∨ m.src.StrictlyBetween m.dst u ∨ u = m.dst →
      ¬ p.board.Attacks p.toMove.other u

/-- The move `m` is legal in the position `p` (Art. 3): it moves a piece of the side to move to
a square not occupied by a piece of the same colour, following the movement rules of the piece
(with a clear path for queens, rooks and bishops), or it is a castling move or a pawn move;
only pawns promote; and the king of the side to move is not left in check (Art. 3.9.2). -/
def IsLegal (p : Position) (m : Move) : Prop :=
  ∃ pc, p.board m.src = some pc ∧ pc.color = p.toMove ∧
    (∀ q, p.board m.dst = some q → q.color ≠ p.toMove) ∧
    (if pc.type = .pawn then p.PawnMove m
      else m.promotion = none ∧
        ((pc.type.Pattern m.src m.dst ∧ p.board.PathClear m.src m.dst) ∨
          (pc.type = .king ∧ p.Castles m))) ∧
    ¬ (p.play m).board.InCheck p.toMove

/-- Two positions are the same in the sense of Art. 9.2.2: the same player has the move, the
same pieces occupy the same squares, the castling rights are the same, and the possible moves
are the same (which accounts for en passant captures). -/
def Same (p q : Position) : Prop :=
  p.board = q.board ∧ p.toMove = q.toMove ∧ p.castling = q.castling ∧
    ∀ m, p.IsLegal m ↔ q.IsLegal m

instance (p : Position) (m : Move) : Decidable (p.PawnMove m) := by unfold PawnMove; infer_instance
instance (p : Position) (m : Move) : Decidable (p.Castles m) := by unfold Castles; infer_instance
instance (p : Position) (m : Move) : Decidable (p.IsLegal m) := by unfold IsLegal; infer_instance
instance (p q : Position) : Decidable (p.Same q) := by unfold Same; infer_instance

end Position

/- ### Games -/

/-- The possible results of a game. -/
inductive Outcome
  | win (c : Color)
  | draw
  deriving DecidableEq

/-- The state of a game: the current position, the positions that occurred earlier in the game,
and the number of half-moves since the last capture or pawn move. -/
structure GameState where
  /-- The current position. -/
  pos : Position
  /-- The positions that occurred earlier in the game, most recent first. -/
  past : List Position
  /-- The number of half-moves played since the last capture or pawn move. -/
  halfmoveClock : ℕ

namespace GameState

/-- The state after the move `m` is played. -/
def play (s : GameState) (m : Move) : GameState where
  pos := s.pos.play m
  past := s.pos :: s.past
  halfmoveClock :=
    if (∃ pc, s.pos.board m.src = some pc ∧ pc.type = .pawn) ∨ s.pos.board m.dst ≠ none then
      0
    else s.halfmoveClock + 1

/-- The number of times the current position has appeared in the game (Art. 9.2.2). -/
def repetitions (s : GameState) : ℕ := (s.past.countP fun q => decide (s.pos.Same q)) + 1

/-- The result of the game if it has ended in the state `s` (Art. 5 and 9.6). The side to move
has no legal move exactly when it is checkmated, if its king is in check, or stalemated, if not.
Otherwise the game is drawn if the same position has appeared at least five times or if the
last 75 moves by each player were made without a capture or pawn move. -/
def result (s : GameState) : Option Outcome :=
  if ∀ m, ¬ s.pos.IsLegal m then
    if s.pos.board.InCheck s.pos.toMove then some (.win s.pos.toMove.other) else some .draw
  else if 5 ≤ s.repetitions ∨ 150 ≤ s.halfmoveClock then some .draw
  else none

/-- The player to move may claim a draw (Art. 9.2 and 9.3): the same position has appeared at
least three times, or the last 50 moves by each player were made without a capture or pawn move,
or the player has a legal move after which one of these holds. -/
def CanClaimDraw (s : GameState) : Prop :=
  3 ≤ s.repetitions ∨ 100 ≤ s.halfmoveClock ∨
    ∃ m, s.pos.IsLegal m ∧ (3 ≤ (s.play m).repetitions ∨ 100 ≤ (s.play m).halfmoveClock)

instance (s : GameState) : Decidable s.CanClaimDraw := by unfold CanClaimDraw; infer_instance

end GameState

/-- `CanForceWin c s` means that player `c` has a strategy that wins the game from the state `s`
against every play of the opponent. As the least predicate closed under the three rules below,
it holds exactly when `c` can force a win in finitely many moves: either the game has ended with
a win for `c`; or `c` is to move and some legal move leads to a state from which `c` can force a
win; or the opponent is to move, cannot claim a draw, and every legal reply leads to a state from
which `c` can force a win. A player who can claim a draw is assumed to do so when it prevents a
loss, and a player who is trying to win never claims a draw. -/
inductive CanForceWin (c : Color) : GameState → Prop
  | won {s : GameState} : s.result = some (.win c) → CanForceWin c s
  | move {s : GameState} (m : Move) : s.result = none → s.pos.toMove = c → s.pos.IsLegal m →
      CanForceWin c (s.play m) → CanForceWin c s
  | reply {s : GameState} : s.result = none → s.pos.toMove = c.other → ¬ s.CanClaimDraw →
      (∀ m, s.pos.IsLegal m → CanForceWin c (s.play m)) → CanForceWin c s

/-- The pieces on the first rank in the initial position, from the a-file to the h-file. -/
def backRank : Fin 8 → PieceType
  | 0 => .rook
  | 1 => .knight
  | 2 => .bishop
  | 3 => .queen
  | 4 => .king
  | 5 => .bishop
  | 6 => .knight
  | 7 => .rook

/-- The initial position (Art. 2.3): White has the move, both players have both castling rights,
and there is no en passant square. -/
def initialPosition : Position where
  board s :=
    if s.rank = 0 then some ⟨.white, backRank s.file⟩
    else if s.rank = 1 then some ⟨.white, .pawn⟩
    else if s.rank = 6 then some ⟨.black, .pawn⟩
    else if s.rank = 7 then some ⟨.black, backRank s.file⟩
    else none
  toMove := .white
  castling _ _ := true
  enPassant := none

/-- The state at the start of a game. -/
def initialState : GameState where
  pos := initialPosition
  past := []
  halfmoveClock := 0

open scoped Classical in
/-- The outcome of chess under perfect play: White wins if White can force a win, Black wins if
Black can force a win, and otherwise the game is a draw. Since chess is a finite game, by
Zermelo's theorem exactly one of these three cases occurs, and in the last case both players
can force at least a draw. -/
noncomputable def perfectPlayOutcome : Outcome :=
  if CanForceWin .white initialState then .win .white
  else if CanForceWin .black initialState then .win .black
  else .draw

/-- White has exactly $20$ legal moves in the initial position. -/
@[category test, AMS 91]
theorem card_filter_isLegal_initialPosition :
    (Finset.univ.filter initialPosition.IsLegal).card = 20 := by
  native_decide

/-- The game has not ended in the initial state. -/
@[category test, AMS 91]
theorem result_initialState : initialState.result = none := by
  native_decide

/-- Fool's mate: after 1. f3 e5 2. g4 Qh4# Black has won. -/
@[category test, AMS 91]
theorem result_foolsMate :
    ((((initialState.play ⟨⟨5, 1⟩, ⟨5, 2⟩, none⟩).play
      ⟨⟨4, 6⟩, ⟨4, 4⟩, none⟩).play
      ⟨⟨6, 1⟩, ⟨6, 3⟩, none⟩).play
      ⟨⟨3, 7⟩, ⟨7, 3⟩, none⟩).result = some (.win .black) := by
  native_decide

/-- After 1. Nf3 Nf6 2. Ng1 Ng8 has been played three times the game goes on, but the fourth
repetition makes the initial position appear for the fifth time and the game is drawn. -/
@[category test, AMS 91]
theorem result_knightShuffle :
    ((fun s : GameState => (((s.play ⟨⟨6, 0⟩, ⟨5, 2⟩, none⟩).play
      ⟨⟨6, 7⟩, ⟨5, 5⟩, none⟩).play
      ⟨⟨5, 2⟩, ⟨6, 0⟩, none⟩).play
      ⟨⟨5, 5⟩, ⟨6, 7⟩, none⟩)^[3] initialState).result = none ∧
    ((fun s : GameState => (((s.play ⟨⟨6, 0⟩, ⟨5, 2⟩, none⟩).play
      ⟨⟨6, 7⟩, ⟨5, 5⟩, none⟩).play
      ⟨⟨5, 2⟩, ⟨6, 0⟩, none⟩).play
      ⟨⟨5, 5⟩, ⟨6, 7⟩, none⟩)^[4] initialState).result = some .draw := by
  native_decide

/--
What is the outcome of a perfectly played game of chess, played from the standard initial
position under the FIDE Laws of Chess? The consensus answer is that chess is a draw with best
play, i.e. `perfectPlayOutcome = .draw`; the minority view is `perfectPlayOutcome = .win .white`.
-/
@[category research open, AMS 91]
theorem first_move_advantage_in_chess : perfectPlayOutcome = answer(sorry) := by
  sorry

/--
The consensus among players and theorists (Steinitz, Lasker, Capablanca, Fischer, Kasparov,
Watson, Rowson, Short): with perfect play chess is a draw, i.e. neither White nor Black can
force a win from the standard initial position.
-/
@[category research open, AMS 91]
theorem first_move_advantage_in_chess.variants.draw : perfectPlayOutcome = .draw := by
  sorry

end FirstMoveAdvantageInChess
