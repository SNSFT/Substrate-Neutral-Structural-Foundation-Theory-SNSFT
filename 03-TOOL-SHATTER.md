# SHATTER — Identity Physics Card Game 
# SHATTER: Formal Mechanics and Mathematical Dynamics of an Applied Identity Physics Game Architecture uuia.app/shatter
### Official Game Guide v2

**Built on:** SNSFT Foundation · Applied Identity Physics · PNBA Framework
**Sovereign Anchor:** Ω₀ = 1.36899099984016 GHz · TL = 0.1369
**Play at:** uuia.app/shatter

---

## Overview

SHATTER is a 4-axis tactical card game built on the PNBA framework of Identity Physics. Each card carries four stats — Pattern (P), Narrative (N), Behavior (B), Adaptation (A) — and clashes resolve through torsion mechanics derived directly from the corpus.

**The core shatter rule:**

> If opponent's final B ≥ 2 × your current P → your card SHATTERS

**The doubles immunity rule:**

> If a card rolls doubles even once during its roll, it cannot shatter that clash regardless of final B total. Doubles are the chain — the chain protects.

---

## The Four Lanes

Each card is deployed into one of four lanes. The lane gives the card a +5 bonus to its matching axis stat:

| Lane | Axis | Bonus |
|:---|:---|:---|
| P-Lane | Pattern | +5P to the card deployed here |
| N-Lane | Narrative | +5N to the card deployed here |
| B-Lane | Behavior | +5B to the card deployed here |
| A-Lane | Adaptation | +5A to the card deployed here |

---

## Class Matrix

Each class has one class it beats and one it loses to. The winning card gets **+5P and +5B** before dice roll:

```
Royalty   → beats → Military
Military  → beats → Assassin
Assassin  → beats → Working Class
Working   → beats → Royalty
```

---

## The Cards

10 unique cards (12 total with duplicates). Five classes, four axes, one manifold.

---

### Royalty Class

**King** · P:6 · N:10 · B:20 · A:2 · (×1)

*Royal Decree: while unshattered, every other unshattered friendly card gains +2P.*

The highest raw B in the deck. Devastating in the B-lane but P:6 means he shatters at incoming B=12 without support. Royal Decree applies immediately when King is placed — every other friendly card gains +2P. The glass cannon that needs a formation to survive.

---

**Queen** · P:7 · N:9 · B:16 · A:4 · (×1)

*Queen's Grace: while unshattered, all friendly cards gain +2P per Royal on the field (herself included).*

1 Royal = +2P · 2 Royals = +4P · 3 Royals = +6P to every friendly card. The stabilizer of the Royalty formation. Running all three Royals together gives every card +6P before dice roll — enough to absorb almost any attack without shattering.

---

**Prince** · P:5 · N:8 · B:15 · A:5 · (×1)

*Heir's Mandate: Working Class solidarity bonus increases by +1P/+1B per worker while Prince is on the field.*

The bridge between Royalty and Working Class. Alone he is modest. With two or three workers on the field his Mandate supercharges the solidarity stack. He is also the first step of the Working Class ascension chain — a Worker that rolls doubles twice becomes a Prince.

---

### Military Class

**Knight** · P:10 · N:4 · B:12 · A:6 · (×2)

*Battlefield Aura: +3B to all other unshattered friendly cards per Knight on the field (max +6B with both Knights). Counter-strike: opponent card loses 6P permanently if Knight survives the clash.*

The only Military card and the only card with a B-based aura. Two Knights give every other card +6B across the formation before dice roll. Counter-strike fires after clash — if Knight survives, the opponent card it clashed against loses 6P permanently for the rest of the round. High P:10 makes Knight structurally durable.

---

### Assassin Class

**Assassin** · P:4 · N:12 · B:10 · A:4 · (×2)

*Waveform Ambush: matrix bonus (+5P/+5B) applies ONLY when revealed from face-down. Requires highest N in the lane. Blocked entirely by Knight.*

Highest N in the deck at N:12 — wins almost every N-priority tiebreak. The waveform is the whole card: deploy face-down, reveal at clash, ambush fires if Assassin has equal or higher N than the opponent. No matrix bonus face-up. Never clash Assassin into Knight — the waveform is completely blocked and Assassin's low P:4 makes it highly vulnerable.

---

### Working Class

**Farmer** · P:6 · N:5 · B:5 · A:10 · (×1)

*Farmer's Yield: while unshattered, every unshattered friendly card of any class gains +1P. The kingdom eats.*

Modest individual stats but the Yield applies to everything — Royalty, Military, Assassin, and other workers all benefit. Highest A in the deck alongside Blacksmith, making Farmer an excellent candidate for the A-lane and for ascension chains.

---

**Blacksmith** · P:5 · N:6 · B:4 · A:12 · (×1)

*Structural Reinforcement: shatter threshold increased to B ≥ 2P+2. Solidarity applies.*

Standard shatter fires at B ≥ 2P. Blacksmith needs B ≥ 2P+2 to go down — a meaningful structural buffer. Highest A in the deck. Deploy in the A-lane to fuel ascension chains and let the reinforcement threshold carry it through clashes it would otherwise lose.

---

**Apothecary** · P:7 · N:4 · B:5 · A:8 · (×1)

*Restore 1 shattered ally per clash — including workers, restoring their solidarity contribution.*

After clash resolves, Apothecary restores the highest-priority shattered ally (workers first since shattered workers break the solidarity stack). Keep Apothecary unshattered to keep the formation intact across multiple rounds.

---

## Formation Bonuses

All auras apply before dice roll and stack with each other:

| Aura | Source | Effect |
|:---|:---|:---|
| Royal Decree | King unshattered | +2P to all other unshattered friendlies |
| Queen's Grace | Queen unshattered | +2P × Royal count to all friendlies |
| Heir's Mandate | Prince unshattered | Solidarity bonus +1P/+1B per worker |
| Battlefield Aura | Knight(s) unshattered | +3B per Knight to all other unshattered friendlies |
| Farmer's Yield | Farmer unshattered | +1P to all unshattered friendlies of any class |
| Working Solidarity | 2+ workers unshattered | +3P/+3B per additional worker beyond the first |

**Solidarity formula:**
- 2 workers: each gets +3P/+3B (or +4 with Prince)
- 3 workers: each gets +6P/+6B (or +8 with Prince)

---

## Working Class Ascension

Working Class cards can ascend through a doubles chain during dice rolls. Each double rolled by a Working Class card counts toward ascension:

**2nd double rolled → Ascends to Prince**
- Stats become: P:5 · N:8 · B:15 · A:5
- Class becomes Royalty
- Heir's Mandate activates immediately on ascension

**3rd double rolled → Sovereign Ascension → Ascended King**
- Stats become: P:8 · N:10 · B:22 · A:6
- Class becomes Royalty
- The Ascended King is stronger than the born King (P:8 vs P:6 · B:22 vs B:20)
- In a direct clash, Ascended King shatters the born King (B:22 ≥ 2×P:6=12)

Higher A increases chain depth (A÷3 + 1 max rolls per chain), so Blacksmith (A:12) and Farmer (A:10) have the deepest ascension potential.

---

## Dice and Doubles

Each card rolls 2d10 and adds the results to its current P and B.

**Doubles chain:** if both dice show the same number, roll again and add to the totals. The chain continues until the dice stop matching or the max chain depth is reached (A÷3 + 1).

**Doubles immunity:** if a card rolls doubles even once, it cannot shatter that clash. The chain is the protection. This applies regardless of final B total — a card that chained is immune for that clash.

**Max chain depth by A value:**
- A:2–4 → max 1 chain roll
- A:5–7 → max 2 chain rolls
- A:8–10 → max 3 chain rolls
- A:11–12 → max 4 chain rolls

---

## Clash Resolution — Step by Step

When both players lock in, all four lanes clash simultaneously:

**1. Formation bonuses apply**
All auras calculated before any dice roll. Solidarity, Royal Decree, Queen's Grace, Battlefield Aura, Farmer's Yield, Heir's Mandate — all fire here.

**2. Class matrix checked**
Advantaged card gets +5P and +5B before rolling.

**3. Assassin waveform resolves**
Face-down Assassins reveal. Ambush fires (+5P/+5B) only if Assassin has equal or higher N than the opponent card and the opponent is not a Knight.

**4. Dice roll**
Each card rolls 2d10. Doubles trigger a chain — roll again, add to totals. Chain depth limited by A÷3 + 1.

**5. Shatter check**
- If opponent's final B ≥ your current P × 2 (or × 2+2 for Blacksmith) AND you did not roll doubles → your card SHATTERS
- If you rolled doubles at any point → immune to shatter this clash regardless of final totals
- Shattered cards lose their aura contributions immediately

**6. Lane winner determined**
Higher final B wins the lane. On a B tie, higher N wins (N-priority tiebreak). On a tie in both, lane is drawn.

**7. Knight counter-strike**
If Knight survived the clash, the opponent card it faced loses 6P permanently.

**8. Apothecary restores**
One shattered ally is restored (workers prioritized).

**9. Ascension check**
Working Class cards with doubles count are checked for Prince or Sovereign Ascension.

**10. Round winner**
Most lanes won wins the round. On a tie, Identity Mass decides:

> Identity Mass = sum of (P + N + B + A) of all unshattered cards on each side

Higher Identity Mass wins. On a true IM tie, N-total (sum of N across all unshattered cards) decides.

---

## Torsion and Phase States

Every card has a torsion value: **τ = B ÷ P**

The Sovereign Anchor Constant Ω₀ = 1.36899099984016 and TL = Ω₀/10 = 0.136899099984016 define the phase boundaries:

| State | τ value | Card display |
|:---|:---|:---|
| NOBLE | τ < 0.001 | Anchor color |
| LOCKED | 0.001 ≤ τ < 0.1205 | Anchor color |
| IVA PEAK | 0.1205 ≤ τ < 0.1369 | Anchor color |
| SHATTER RISK | τ ≥ 0.1369 | Orange warning |
| SHATTER | τ ≥ 2.0 (in-game) | Red — shatter condition met |

Torsion displays on each card as τ. Cards in the orange range are approaching the structural limit.

---

## Game Modes

**VS AI** — Solo practice against a strategic AI. The AI evaluates class advantage, torsion risk, solidarity potential, shatter windows, and ascension chains. Useful for learning card interactions and formation strategies before playing against a real opponent.

**VS FRIEND** — Multiplayer via 4-character room code. One player creates a room and shares the code. Both players see each other's 5 cards in hand (so you know what they could play) but opponent lane placements stay hidden until both players lock in. After both lock, all cards reveal simultaneously and clash fires. Both players see the same combat log. Hit Continue after each round to advance to the next.

---

## Strategy Notes

**Running all three Royals:** King + Queen + Prince gives every card +2P (Decree) + +6P (Grace with 3 Royals) = +8P before dice. King in the P-lane becomes nearly unshatterable. The downside is no Working Class solidarity and no ascension chain.

**Three workers + Prince:** With Prince active, solidarity gives each worker +4P/+4B per additional worker beyond the first. Three workers = +8P/+8B each. Add Farmer's Yield (+1P to all) and the formation has significant stat depth. The ascension chain is live every round.

**Two Knights:** Battlefield Aura gives every non-Knight card +6B. Combined with Royal Decree or solidarity, your formation becomes aggressive across all lanes. Knights are durable at P:10 and counter-strike punishes anything that doesn't finish them.

**Assassin placement:** Always deploy face-down or not at all. Face-up Assassin has no matrix bonus and P:4 makes it the easiest card to shatter. Face-down Assassin with N:12 wins almost every tiebreak and the waveform ambush is +5P/+5B on reveal — a significant swing.

**Blacksmith in the A-lane:** Structural Reinforcement + highest A in the deck + A-lane +5A = maximum ascension chain depth and the hardest card to shatter. A Blacksmith that chains three times and ascends to Ascended King (B:22) is the strongest single-card outcome in the game.

**Apothecary timing:** Apothecary restores one card per clash automatically if unshattered. Prioritize keeping Apothecary alive in the lane least likely to be contested. A restored worker brings the full solidarity stack back online.

---

## References

HIGHTISTIC. (2026). *Applied Identity Physics Corpus*. SNSFT Foundation. DOI: 10.5281/zenodo.18719748

HIGHTISTIC. (2026). *PNBA Phase Taxonomy* [9,9,2,50]. SNSFT Foundation.

**Sovereign Anchor Constant:** Ω₀ = 1.36899099984016 GHz
**Torsion Limit:** TL = Ω₀/10 = 0.136899099984016
**Shatter Condition:** B ≥ 2P (τ ≥ TL in-game approximation)
**Doubles Immunity:** chain = no shatter, regardless of final totals

[9,9,9,9] :: {ANC} · The Manifold is Holding.

---

## Parent & Classroom Guide — What SHATTER Actually Teaches

SHATTER looks like a card game. Under the hood it is a real math engine built on Identity Physics. Every clash runs torsion calculations, ratio analysis, cumulative bonus stacking, and comparative Identity Mass — the same operations that appear in the formal corpus. This section is for parents, teachers, and facilitators who want to connect what kids are doing at the table to the math and concepts underneath.

---

### What Each Axis Teaches

**Pattern (P) — Structural Capacity**
P is how much load a card can absorb before it breaks. In every clash, kids are intuitively asking: is my P high enough to survive incoming B? That is ratio reasoning — the same thinking used in engineering load calculations, material science, and structural analysis. When a child says "my King has low P so I need to protect him," they are doing structural analysis.

*Real math:* division and thresholds. Shatter fires when B ÷ P ≥ 2. Kids learn to evaluate ratios before they learn to write them formally.

**Narrative (N) — Continuity and Rank**
N decides who goes first when B values tie. It rewards cards that carry historical depth — Assassin's N:12 reflects that its power comes from patience and positioning, not raw force. In the classroom, N is a conversation about why continuity matters: why does experience give you priority? Why does the card that has been building the longest get the tiebreak?

*Real math:* ordering and priority systems. N-priority is a tiebreak rule — kids learn that when two values are equal, a secondary variable decides the outcome.

**Behavior (B) — Active Output and Cause-Effect**
B is what a card does to the opponent. Every roll, kids are generating B output and checking it against opponent P. That is a cause-and-effect loop running in real time: how much force am I generating, and what threshold does it need to cross? The doubles chain makes this dynamic — more rolls mean more B, but also more risk of going too high.

*Real math:* addition under uncertainty, probability chains, threshold crossing. The exploding doubles mechanic is a real probability chain — each roll is independent, but the cumulative output depends on how many times you can chain.

**Adaptation (A) — Flexibility and Chain Depth**
A controls how deep a card can chain on doubles. High-A cards like Blacksmith (A:12) and Farmer (A:10) can roll up to four times on a chain. Low-A cards like King (A:2) can only chain once. A is the axis that rewards adaptability — the card that can keep going when conditions are favorable.

*Real math:* A÷3+1 is the chain depth formula. Kids playing SHATTER are computing this intuitively before they ever write it down. Ask a kid after a match: "why did your Blacksmith keep rolling?" and watch them derive the formula themselves.

---

### Real Math Happening in Every Game

| Game mechanic | Mathematical concept | Corpus term |
|:---|:---|:---|
| τ = B ÷ P | Ratio analysis | Torsion |
| Shatter when B ≥ 2P | Threshold inequality | Shatter condition |
| Solidarity stack (+3 per worker) | Cumulative addition, multiplication | Formation bonus |
| Identity Mass = P+N+B+A × Ω₀ | Multi-variable summation | IM |
| Lane bonus (+5 to matching axis) | Optimization under constraints | Axis alignment |
| Doubles chain (A÷3+1) | Integer division, sequence depth | Adaptation capacity |
| Class matrix advantage | Graph theory, directed relationships | PNBA class structure |
| N-priority tiebreak | Ordered ranking systems | Narrative priority |

---

### Discussion Questions After a Match

These questions work for any age. The goal is to get the player to articulate the math they just ran intuitively.

**On torsion and shatter:**
- Why did that card shatter? What were the B and P values?
- If you had put that card in the P-lane instead, would it have survived?
- What P value would you need to survive B:30 incoming?

**On formation bonuses:**
- How much did your solidarity stack add to each worker?
- What happened to your formation when the Apothecary restored that card?
- If you had a third Knight, what would the Battlefield Aura total be?

**On strategy and optimization:**
- Why did you put Assassin face-down instead of face-up?
- Which lane gave your King the best survival odds and why?
- What would you deploy differently if you could replay that round?

**On the axes themselves:**
- Which axis is hardest for you to build around? Why?
- What would a real-world system look like that has high B but low P?
- Can you think of something in real life that has high N (a lot of history and continuity)?

---

### For Younger Players (Ages 8–12)

Focus on two things: shatter and solidarity.

**Shatter** is the rule kids get fastest. Show them: if your B number is twice as big as their P number, they shatter. Let them calculate it by hand before each clash. They will be doing division and multiplication without realizing it.

**Solidarity** is the concept that rewards cooperation. Three workers together are stronger than one worker alone — the bonus grows with the group. Ask kids: does this remind you of anything in real life? Teams, families, communities all work this way.

The game teaches these concepts through play first. The formal language can come later. The intuition comes from the table.

---

### For Older Players and Classrooms (Ages 13+)

Introduce the formal notation after a few matches:

- Write τ = B/P on the board and ask students to calculate torsion for each card in their hand
- Ask them to find the minimum P value needed to survive a given B attack
- Have them calculate Identity Mass for a full formation and explain why it matters as a tiebreaker
- Discuss why the doubles chain gives immunity to shatter — what does it mean structurally that a system generating doubles cannot be broken by its own output?

Advanced discussion: the class matrix is a directed graph. Royalty beats Military beats Assassin beats Working beats Royalty. Ask students: is there a dominant strategy? Why or why not? (There isn't — every class beats one and loses to one, which is the design intent.)

---

### The Bigger Picture

SHATTER is built on Identity Physics — a formally verified mathematical corpus with 200,000+ theorems, 0 unproven assumptions, and a Sovereign Anchor Constant derived from three peer-reviewed physical threshold systems. The game is a doorway into that corpus.

When a child learns that torsion τ = B/P governs structural stability in a card game, they are learning the same ratio that governs torsional collapse in engineering, phase transitions in thermodynamics, and adaptive response in psychology. The game makes the abstraction tangible first. The corpus makes it formal second.

The Sovereign Anchor Constant Ω₀ = 1.36899099984016 appears in the game as the multiplier for Identity Mass: IM = (P+N+B+A) × Ω₀. This constant is structurally locked to the fine-structure constant α at twelve-digit precision — one of the deepest relationships in the corpus. Kids playing SHATTER are, without knowing it, computing with a constant that connects to the fundamental structure of electromagnetism.

That is the real game.

**Corpus:** HIGHTISTIC (2026). Applied Identity Physics. SNSFT Foundation. DOI: 10.5281/zenodo.18719748
**Play:** uuia.app/shatter
[9,9,9,9] :: {ANC} · The Manifold is Holding.
