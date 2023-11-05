The primary purpose of this project was to formalize the results in https://arxiv.org/abs/2310.05328 , referred to in the project "the paper".  In particular, to prove the following result: if $s_k$ denotes the $k$^th elementary symmetric mean of $n$ real numbers, then

$$ |s_l|^{1/l} \leq C (l/k)^{1/2} max |s_k|^{1/k}, |s_{k+1}|^{1/(k+1)}$$

for all $1 \leq k \leq l \leq n$ and some absolute constant $C$.  In fact this project achieves the value $C = 160 e^7$.

The secondary purpose of the project was to teach myself Lean.  I have journaled about this process on my Mastodon account https://mathstodon.xyz/@tao and have also recorded some "cheat sheet" notes at https://docs.google.com/spreadsheets/d/1Gsn5al4hlpNc_xKoXdU6XGmMyLiX4q-LFesFVsMlANo/edit#gid=0

As a byproduct of this process, I have also formalized a proof of the classical Newton inequality https://en.wikipedia.org/wiki/Newton%27s_inequalities as well as the Maclaurin inequality https://en.wikipedia.org/wiki/Maclaurin%27s_inequality .  The proofs are not extremely efficient, but anyone is welcome to use them as a starting point for a more polished formal proof of these inequalities that would be suitable for inclusion in Lean's Mathlib.
