.PHONY: verify regenerate replay
verify:
	python3 verify_certificate.py
	python3 independent_check.py
regenerate:
	g++ -O2 -std=c++17 -Wall -Wextra -pedantic build_certificate.cpp -o build_certificate
	./build_certificate > generation.json
	python3 verify_certificate.py
replay:
	python3 clean_replay.py
