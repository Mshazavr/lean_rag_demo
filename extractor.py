
from dataclasses import dataclass
import torch 
import pickle
import numpy as np
from numpy.linalg import norm
from transformers import AutoTokenizer, AutoModel
from tqdm import tqdm
import logging

logging.getLogger("transformers").setLevel(logging.ERROR)

# EMBEDDING_MODEL = "math-similarity/Bert-MLM_arXiv-MP-class_zbMath"
EMBEDDING_MODEL = "kaiyuy/leandojo-lean4-retriever-byt5-small"

LEAN_SOURCE_NAME = "nat_basic.lean"
THEOREM_NAMES_OUT = "nat_basic_names.txt"
THEOREM_TEXTS_OUT = "nat_basic_texts.txt"

QUERY_TEXT = "theorem simple (a b c : Nat) : a + (b * c) = (b * c) + a := by"

def log(text: str):
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    ENDC = '\033[0m'

    print(OKCYAN + ">>>" + ENDC + " " + text)


class EmbeddingRetriever:
    def __init__(self, vector_keys: list[str], vectors: list[np.ndarray]):
        self._vector_keys = vector_keys
        self._vectors = vectors
    
    @staticmethod
    def vector_similarity(v1: np.ndarray, v2: np.ndarray):
        return np.dot(v1, v2) / (norm(v1) * norm(v2))

    def retrieve_top_k(self, query: np.ndarray, k: int = 10):
        similarities = sorted([
            (self.vector_similarity(query, vector), i)
            for i, vector in enumerate(self._vectors)
        ])

        for sim, i in similarities:
            log(f"{'{:.4f}'.format(round(sim, 4))} : {self._vector_keys[i]}")

        top_k_keys = [
            self._vector_keys[i]
            for _, i in reversed(similarities[-k:])
        ]
        return top_k_keys


class Embeddor:
    def __init__(self, huggingface_model_name: str):
        self._tokenizer = AutoTokenizer.from_pretrained(huggingface_model_name)
        self._model = AutoModel.from_pretrained(huggingface_model_name).encoder
    
    def embed(self, text: str):
        encoded_input = self._tokenizer(
            text, padding=True, truncation=True, return_tensors='pt'
        )

        with torch.no_grad():
            model_output = self._model(**encoded_input)

        sentence_embedding = self.mean_pooling(
            model_output, encoded_input['attention_mask']
        )
        return sentence_embedding[0].numpy()

    @staticmethod
    def mean_pooling(model_output, attention_mask):
        last_hidden_state = model_output.last_hidden_state
        input_mask_expanded = attention_mask.unsqueeze(-1).expand(
            last_hidden_state.size()
        ).float()
        sum_embeddings = torch.sum(last_hidden_state * input_mask_expanded, 1)
        sum_mask = torch.clamp(input_mask_expanded.sum(1), min=1e-9)
        return sum_embeddings / sum_mask



@dataclass
class Theorem:
    key: str
    text: str

def get_theorem_list_lean_syntax(theorem_keys: list[str]):
    result = (
        "[\n" + 
        ",\n".join([f"  {key}" for key in theorem_keys]) +
        "\n]"
    )
    return result

def parse_theorems() -> list[Theorem]:
    lean_source_lines = []
    with open(LEAN_SOURCE_NAME, "r") as f:
        lean_source_lines = f.readlines()

    theorems : list[Theorem] = []
    for line in lean_source_lines:
        if line.startswith("theorem"):
            theorems.append(
                Theorem(
                    key="Nat." + line.split()[1].strip(),
                    text=line
                )
            )
        elif line.startswith("protected theorem"):
            theorems.append(
                Theorem(
                    key="Nat." + line.split()[2].strip(),
                    text=line[10:]
                )
            )

    with open(THEOREM_NAMES_OUT, "w") as f:
        f.write(
            get_theorem_list_lean_syntax(
                [theorem.key for theorem in theorems]
            )
        )

    return theorems

def get_embeddings(embeddor: Embeddor, theorems: list[Theorem], cached_embeddings: bool = False):
    if not cached_embeddings:
        embeddings = [embeddor.embed(theorem.text) for theorem in tqdm(theorems)]
        with open("embeddings.pkl", "wb") as f:
            pickle.dump(embeddings, f)
    else:
        with open("embeddings.pkl", "rb") as f:
            embeddings = pickle.load(f)
    
    return embeddings

def main(cached_embeddings: bool = False):
    log("Parsing theorems...")
    theorems = parse_theorems()
    log("Done parsing theorems ✓")

    log("Loading embedding model...")
    embeddor = Embeddor(EMBEDDING_MODEL)
    log("Done loading embedding model ✓")

    log("Computing embeddings...")
    embeddings = get_embeddings(embeddor, theorems, cached_embeddings)
    log("Done computing embeddings ✓")

    retriever = EmbeddingRetriever(
        vector_keys=[theorem.key for theorem in theorems],
        vectors=embeddings
    )

    log("Retrieving top 10 theorems...")
    top_10_theorems = retriever.retrieve_top_k(
        query=embeddor.embed(QUERY_TEXT),
        k=10
    )
    log("Done retrieving ✓")

    log("Results:")
    log(get_theorem_list_lean_syntax(top_10_theorems))