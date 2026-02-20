import os

def test_readme_present():
    assert os.path.exists("README.md")


def test_readme_title():
    with open("README.md", "r", encoding="utf-8") as f:
        content = f.read()
    assert "Human-First-Protocol-Hardware-Formal-Verification-Academic-Foundation" in content
