this repository solves the open problem in https://arxiv.org/abs/2412.07318 formalizing the proof in https://doi.org/10.5281/zenodo.20350558.
there are custom axioms. however, all of the custom axioms are a valid interpretation of what's proven in literature. 
i provided a PyMuPDF script for easier verification for match between the literature and the axioms. 
the script passed when ran on google colab free tier with the only dependency being the need to install weasyprint and PyMuPDF.
there's a sorry in the Challenge.lean. however, the proof is not ungiven. the sorry statement is intended to be the problem statement which is solved in the Solution.lean file with the full proof. 
Additionally, i verified the proof via proofQED/QED and dropped the output and instructions in the pull request from this repository to the same repository.
the output was useful for clear natural language readability of the steps and it's advised to read the pull request for instructions regarding the QED verification branch of the repository 
