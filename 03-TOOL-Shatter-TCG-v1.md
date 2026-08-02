# SHATTER: An Educational 4-Axis Card Game for Teaching Vector Math, Ratios & Probabilistic Reasoning

**System Design & Learning Framework**

*Russell Trent — HighTistic Architecture / Identity Physics*
*Formal Framework: Substrate-Neutral Structural Foundation Theory (SNSFT)*

---

## Abstract

**SHATTER** is a deterministic 1-v-1 tactical card game built to make abstract math *tangible* through play. Every card is a 4-dimensional stat vector — Shield (**P**), Rank (**N**), Attack (**B**), and Ability (**A**) — and every clash resolves through the same handful of operations: vector addition, ratio comparison, and conditional thresholds. Rather than hiding the math behind flavor text, SHATTER puts it on the table: players read off numbers, add modifiers, compute a ratio, and compare it to a fixed limit to see if a unit **Shatters**.

This document covers the system architecture, the mechanics, and — for anyone using SHATTER as a teaching tool — what each mechanic is actually asking a player to practice.

---

## 1. Introduction & Purpose

Most card games hide their math behind rulebooks and rare-card scarcity. SHATTER does the opposite: it's built so that winning requires understanding *why* the numbers do what they do, not just memorizing card text. That makes it useful as:

- A hands-on intro to **vectors and vector addition** (stat stacking across lane bonuses, class bonuses, support auras, and dice rolls)
- A live demonstration of **ratios and thresholds** (the Shatter condition)
- A gentle, game-based intro to **probability** (why doubles are rare, and why exploding chains taper off)
- A concrete example of a **cyclic/modular relationship** (the 4-way class matrix)
- A simple **finite state machine** (Un-Shattered → Shattered → Ascended), where entering the Shattered state also silences every passive ability tied to that card
- A comparison of **different growth patterns** — flat bonuses vs. bonuses that scale with a headcount (the support-aura family in Section 7)

### Learning Objectives

| Mechanic | Math Concept Practiced |
|---|---|
| $IM = P+N+B+A$ | Vector magnitude via component sum |
| Lane + Class Matrix + Support Aura bonuses | Vector addition, additive modifiers |
| $B \ge 2P$ Shatter check | Ratios, inequalities, threshold logic |
| Exploding double chains | Conditional probability, geometric decay |
| 4-way class cycle | Cyclic/modular relationships (like rock-paper-scissors, but mod 4) |
| Working-Class Solidarity & Royal auras | Linear scaling vs. flat bonuses — comparing growth rates |
| Round-level Identity Mass tiebreak | Summation, comparing aggregate totals |
| Ascension chain | State machines, sequential conditions |

---

## 2. The P-N-B-A Vector

Every card is represented as a state vector in $\mathbb{R}^4$:

$$
\mathbf{C} = \begin{bmatrix} P \\ N \\ B \\ A \end{bmatrix}
$$

- **Shield ($P$):** structural defense — how much attack a unit can absorb before it breaks.
- **Rank ($N$):** timeline priority — decides who wins a tie.
- **Attack ($B$):** kinetic output — direct damage potential.
- **Ability ($A$):** utility frequency — how often a unit can chain bonus effects.

**Identity Mass ($IM$)** is the vector's component sum — a single "how big is this card overall" number:

$$
IM = P + N + B + A
$$

*Teaching note: $IM$ is a simplified stand-in for vector magnitude. If you want to introduce true Euclidean magnitude later ($\|\mathbf{C}\| = \sqrt{P^2+N^2+B^2+A^2}$), SHATTER's card stats are a ready-made dataset to practice on. $IM$ also isn't just a flavor stat — see Section 6.1, where it decides drawn rounds.*

---

## 3. The 4-Way Class Matrix

Units belong to four factions arranged in a closed directional cycle. Being positioned favorably against an opponent's class grants a flat **+5 Matrix Bonus** to both current Shield ($P$) and current Attack ($B$):

$$
\text{Royalty} \xrightarrow{+5} \text{Military} \xrightarrow{+5} \text{Assassins} \xrightarrow{+5} \text{Working-Class} \xrightarrow{+5} \text{Royalty}
$$

- **Royalty beats Military** — structural order dampens raw force.
- **Military beats Assassins** — defensive sweeps neutralize stealth.
- **Assassins beat Working-Class** — surgical strikes exploit local vulnerability.
- **Working-Class beats Royalty** — collective kinetic pressure collapses rigid thrones.

*Teaching note: this is a great low-stakes entry point into modular arithmetic — four classes arranged like a clock face (mod 4), where "who beats whom" is just "am I one step ahead of you around the circle."*

---

## 4. Field Geometry: The 4-Axis Matrix

The board has four lanes crossing a central **Collision Horizon**. Each side may field at most one card per lane (four cards max per player):

1. **P-Axis (Shield Domain):** +2 Shield ($P$) environmental modifier.
2. **N-Axis (Rank Domain):** higher printed Rank ($N$) wins ties in this lane.
3. **B-Axis (Attack Domain):** +2 Attack ($B$) environmental modifier — raises the stakes, since higher $B$ also raises Shatter risk.
4. **A-Axis (Ability Domain):** maximizes exploding-chain stability for high-$A$ units.

*Teaching note: each lane applies its own additive modifier before the clash — a live example of vector addition in a low-dimensional, easy-to-track space.*

---

## 5. Clash Mechanics & State Resolution

### 5.1 Turn Momentum Loop

Players alternate freely between deploying cards (face-up, or face-down as a hidden "waveform") and declaring a clash, until deployment options run out.

### 5.2 Cumulative Exploding Chain Math

At a clash, each side rolls two ten-sided dice ($d_P$, $d_B$). If the unit is Un-Shattered and rolls doubles ($d_P = d_B$), the roll **explodes** — both values are added to the running total, and the unit rolls again:

$$
\Delta B_i = d_{P,i} + d_{B,i}, \qquad \Delta P_i = d_{P,i} + d_{B,i}
$$

Totals accumulate across the whole chain:

$$
B_{\text{Total}} = B_{\text{Base}} + B_{\text{Lane}} + \mathbf{M} + \mathbf{S} + \sum_{i=1}^{k} \Delta B_i
$$
$$
P_{\text{Total}} = P_{\text{Base}} + P_{\text{Lane}} + \mathbf{M} + \mathbf{S} + \sum_{i=1}^{k} \Delta P_i
$$

where $k$ is the number of rolls in the chain, $\mathbf{M}$ is the Class Matrix bonus (Section 3), and $\mathbf{S}$ is the total of any active Support Auras — Working-Class Solidarity, Heir's Mandate, Farmer's Yield, Royal Decree, or Queen's Grace (Section 7).

*Teaching note: this is a natural, hands-on intro to probability. Rolling doubles on 2d10 has a $\frac{1}{10}$ chance per roll, so a chain of $k$ **consecutive** doubles has probability $\left(\frac{1}{10}\right)^{k-1}$ — a clean example of independent events and geometric decay. The chain stops the instant a non-double is rolled, so this is strictly about a run of consecutive hits, not doubles accumulated over the whole game. It's also a good jumping-off point for expected value: "on average, how much extra $B$ does a chain add?"*

### 5.3 The Shatter Limit

At every state check, a unit's structural integrity is evaluated against a fixed ratio:

$$
\text{State}(\mathbf{C}) =
\begin{cases}
\text{Shattered}, & B_{\text{Total}} \ge 2 \times P_{\text{Total}} \; (+2 \text{ if Blacksmith}) \\
\text{Un-Shattered}, & B_{\text{Total}} < 2 \times P_{\text{Total}} \; (+2 \text{ if Blacksmith})
\end{cases}
$$

**Shattered effects:** the card stays on the board, but all passive triggers, class modifiers, Support Auras, and exploding-chain potential switch off — completely, and immediately. If a card's aura was helping other cards earlier in the deploy phase, and that card Shatters partway through the clash sequence, cards resolving in *later* lanes that same clash no longer receive the bonus. Shattering is a status change, not an automatic win — the lane's outcome is still decided by comparing actual stat output (see Section 6).

*Teaching note: $\frac{B}{P} \ge 2$ is just a ratio comparison — the same skill as "is this fraction greater than this other fraction," dressed up as game tension. You can literally have players compute $\tau = B/P$ each clash and watch it against the line at $\tau = 2$. The "abilities switch off the instant you Shatter" rule is also a clean way to talk about state-dependent behavior — the same card behaves differently depending only on its current state, not on anything else about it.*

---

## 6. Lane Resolution

A lane's winner is the side whose $B_{\text{Total}}$ output is higher — **not** automatically whichever side avoided Shattering. If both totals are equal, Rank ($N$) breaks the tie; if still equal, the lane is a draw.

*Teaching note: this separation matters pedagogically — it keeps "did you cross the threshold" (a yes/no inequality check) distinct from "who had the bigger number" (a direct comparison), so the two ideas don't get muddled together in a student's head.*

### 6.1 Round-Level Ties: The Identity Mass Tiebreak

Lane ties and *round* ties are different things. A round is made up of four lane results; it's entirely possible for both sides to win two lanes each. When that happens, the round is **not** simply called a draw — it's resolved by comparing total **Identity Mass** of every currently Un-Shattered card across the whole field:

$$
IM_{\text{side}} = \sum_{\text{unshattered cards } c \text{ on that side}} \left( P_c + N_c + B_c + A_c \right)
$$

using each card's *live*, bonus-included stats at the moment the round ends. Whichever side's total is higher wins the round; if the totals also tie, the round is a genuine draw.

*Teaching note: this is where Section 2's $IM$ stat, introduced early as a simple "how big is this card" number, comes back with real stakes — a nice full-circle moment if you're teaching this sequentially. It also makes the **Apothecary** (Section 7 and Section 8) disproportionately valuable: every ally it keeps Un-Shattered is one more card's full $P+N+B+A$ that still counts toward this sum. A formation that plays defensively and keeps units alive, even at reduced stats, can out-mass an opponent that wins more individual dice rolls but loses more cards along the way.*

---

## 7. Support Auras: Solidarity & Royal Bonuses

Several cards project a passive bonus onto their own side rather than fighting harder themselves. All of them share the same underlying rule from Section 5.3: **the aura is live only while its source card is on the field and Un-Shattered** — the instant that card breaks, the bonus disappears for everyone, immediately, mid-clash if necessary. What differs between them is the *shape* of the bonus — flat, or scaling with a headcount — which makes this section a good place to compare growth patterns side by side.

### 7.1 Working-Class Solidarity

For every *additional* Un-Shattered Working-Class card beyond the first, **every** Un-Shattered Working-Class card on that side gains a bonus to both Shield and Attack:

$$
\text{Solidarity Bonus} = 3 \times (n - 1)
$$

where $n$ is the number of Un-Shattered Working-Class cards on your field ($n \ge 1$; the bonus is $0$ if $n \le 1$).

| Workers on field ($n$) | Bonus per worker |
|:-:|:-:|
| 1 | +0 / +0 |
| 2 | +3P / +3B |
| 3 | +6P / +6B |

**Heir's Mandate (Prince):** while the Prince is Un-Shattered on the field, the per-worker rate rises from $3$ to $4$:

$$
\text{Solidarity Bonus (with Prince)} = 4 \times (n-1)
$$

so 2 workers gives +4 instead of +3, and 3 workers gives +8 instead of +6. The Prince is Royalty, not Working-Class, so he doesn't count toward $n$ himself — he only boosts the rate.

*Teaching note: this is a linear function of headcount, $f(n) = 3(n-1)$, with the Prince changing the slope from $3$ to $4$. A nice board-work exercise: graph $f(n)$ for $n = 1, 2, 3$ with and without the Prince, and ask which grows faster and why.*

### 7.2 Farmer's Yield

While the Farmer is Un-Shattered, **every** Un-Shattered friendly card — any class, not just Working-Class — gains a flat **+1 Shield ($P$)**. Unlike Solidarity, this doesn't scale with how many other cards are on the field; it's a constant, active as soon as the Farmer is deployed, even with no other cards present.

### 7.3 Royal Decree (King) & Queen's Grace

The two Royalty support cards mirror each other but scale differently:

- **Royal Decree (King):** while Un-Shattered, every *other* Un-Shattered friendly card gains a flat **+2 Shield ($P$)** — same shape as Farmer's Yield, just a bigger flat number and restricted to "other" cards (the King himself doesn't get his own bonus).
- **Queen's Grace (Queen):** while Un-Shattered, every Un-Shattered friendly card gains **+1 Attack ($B$) for each Un-Shattered Royalty card on the field**, herself included:

$$
\text{Queen's Grace Bonus} = r
$$

where $r$ is the count of Un-Shattered Royalty cards on that side. With just the Queen alone, $r=1$; with King, Queen, and Prince all Un-Shattered, $r=3$.

*Teaching note: Section 7 as a whole gives you three different bonus shapes to compare directly — Working-Class Solidarity scales with headcount and touches both $P$ and $B$; Farmer's Yield and Royal Decree are flat, touching only $P$; Queen's Grace scales with a *different* headcount (Royalty, not all cards) and touches only $B$. A good discussion question: if you had six cards on the field, which of these bonuses would you want stacking, and why does the answer depend on how many of them are Working-Class vs. Royalty?*

---

## 8. System Registry

| Card | Qty | $P$ | $N$ | $B$ | $A$ | $IM$ | Trait |
|---|:-:|:-:|:-:|:-:|:-:|:-:|---|
| **King** | 1 | 6 | 10 | 20 | 2 | 38 | *Royal Decree*: while Un-Shattered, every other Un-Shattered friendly card gains +2 Shield ($P$). (Section 7.3) |
| **Queen** | 1 | 7 | 9 | 16 | 4 | 36 | *Queen's Grace*: while Un-Shattered, all friendly cards gain +1 Attack ($B$) per Un-Shattered Royalty card on the field, herself included. (Section 7.3) |
| **Prince** | 1 | 5 | 8 | 15 | 5 | 33 | *Heir's Mandate*: while Un-Shattered, raises the Working-Class Solidarity rate from +3 to +4 per additional worker. (Section 7.1) |
| **Knight** | 2 | 10 | 4 | 12 | 6 | 32 | Counter-strike: deals 6 damage to attacker's $P$ if it survives Un-Shattered. |
| **Assassin** | 2 | 4 | 12 | 10 | 4 | 30 | *Waveform Ambush*: Matrix bonus applies only if revealed from face-down. |
| **Farmer** | 1 | 6 | 5 | 5 | 10 | 26 | *Farmer's Yield*: while Un-Shattered, every Un-Shattered friendly card — any class — gains +1 Shield ($P$). (Section 7.2) |
| **Blacksmith** | 1 | 5 | 6 | 4 | 12 | 27 | *Structural Reinforcement*: Shatter threshold raised to $B \ge 2P+2$. Benefits from Solidarity like any Working-Class card. |
| **Apothecary** | 1 | 7 | 4 | 5 | 8 | 24 | Restores 1 Shattered ally to Un-Shattered. The restoration is permanent unless that card Shatters again in a later clash. |

---

## 9. Working-Class Sovereign Ascension

Working-Class units follow a non-linear evolution chain, triggered by consecutive exploding doubles rolled within a single clash's dice chain (Section 5.2):

1. **1st Double:** standard cumulative stat expansion, roll continues.
2. **2nd Double:** mid-combat transition into a **Knight** template ($P=10, N=4, B=12, A=6$).
3. **3rd Double:** **Sovereign Ascension** — the unit permanently becomes a **King** ($P=6, N=10, B=20, A=2$), and gains access to Royal Decree (Section 7.3) from that point forward.

*Teaching note: this is a simple finite state machine — three states, with a single trigger condition (rolling doubles again, in a row, without a miss) moving the unit forward one step at a time. It's a good visual for "state transitions triggered by repeated events," which shows up everywhere from Markov chains to vending-machine logic. Pair it with the probability note in Section 5.2 — ask students how likely it actually is to see three doubles in a row ($10^{-2} = 1\%$ per independent chain), and why Sovereign Ascension is meant to feel rare and dramatic rather than routine.*

---

## 10. Conclusion

SHATTER shows that a tactical card game doesn't need to hide its mechanics behind abstraction to be fun — the math *is* the game. Vector addition determines your stats, a ratio determines whether you break, a cyclic relationship determines your matchups, and a family of scaling and flat bonuses determines how much your teamwork is worth. Played casually, it's a card game. Played deliberately, it's a hands-on lesson in vectors, ratios, probability, growth rates, and state logic — all before anyone touches a textbook.
