# Coq-Elementary-Number-Theory
This repository contains mathematical proofs in Coq, what is Coq?
Coq is a formal proof management system. It provides a formal language to write mathematical definitions, 
executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs.
So basically you can write Math in Coq and it will check if that Math is correct.
Basic mathematical facts when written in such a rigrous way that even a computer can understand, may get decently complicated.
</br> basics.v contains the foundation logic of the Natural numbers, the main arithmetic axioms and the ordering definition,
it also contains basic theorems about arithmetic.
</br> morebasics.v proves that our definition of the natural numbers, based on arithemetic, trichotomy and well ordering principile,
actually defines correctly the natural numbers. Also gives the basic theory of divisibility
</br> euclides.v proves one of the major techniques in elementary number theory which is the algorithm of euclides
</br> bezout.v one of the most important results in elementary number theory
</br> primes.v gives a formal proof for some of the most core theorems about primes, inculding the existence of a factorization about them.
<pre><b>IMPORTANT</b> If you try to run any of the files basics.v, morebasics.v, euclides.v, bezout.v, primes.v on the CoqIDE it will not work, because even though I separated the code for the sake of better reading, one file needs the definitions of the other and that is why there is the file cat.v, which is concatenation of all the previous files, you can actually run cat.v in the COQIDE and it will work.</pre>
