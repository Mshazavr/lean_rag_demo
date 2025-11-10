
import sys
from extractor import main

if __name__ == "__main__":
    cached_embeddings = False
    if "--cached" in sys.argv:
        cached_embeddings = True
    main(cached_embeddings)