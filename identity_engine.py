import sys

def run_test():
    print("="*60)
    print("UUIA IDENTITY ENGINE [PNBA-V1] ::: |ANC| ::: 1.369 GHz")
    print("="*60)
    print("Instructions: Rate each statement from 1 (Not true) to 5 (Very true).")
    print("-"*60)

    sections = {
        "Pattern": [
            "I feel calmer when I know what to expect.",
            "Sudden changes throw me off more than they do other people.",
            "I like having routines, even simple ones.",
            "When things feel chaotic, I get overwhelmed fast.",
            "I notice patterns in people or situations before others do.",
            "I get stressed when plans change last minute.",
            "I prefer clear instructions over vague ones.",
            "I need time to adjust when something unexpected happens.",
            "I feel more confident when things follow a predictable flow.",
            "I struggle when too many things happen at once."
        ],
        "Narrative": [
            "I think a lot about who I am and what I want to be.",
            "I feel connected to certain roles (student, friend, parent, etc.).",
            "When someone questions my choices, it hits me harder than I expect.",
            "I care a lot about how people see me.",
            "I try to make sense of my life by connecting events together.",
            "I feel lost when I don’t know what my 'role' is in a group.",
            "I get upset when I feel misunderstood.",
            "I need my relationships to feel meaningful.",
            "I think about the kind of person I want to become.",
            "When something challenges my identity, I feel shaken."
        ],
        "Behavior": [
            "When I’m stressed, I either shut down or go into overdrive.",
            "I sometimes switch between high energy and low energy quickly.",
            "I get bursts of motivation followed by burnout.",
            "I act without thinking when I feel overwhelmed.",
            "I can go from calm to frustrated fast.",
            "I sometimes avoid things until they become too big to handle.",
            "I get stuck in loops of overthinking or overreacting.",
            "I have days where I feel 'on' and days where I feel 'off.'",
            "I push myself too hard and then crash.",
            "I struggle to stay steady when too much is happening."
        ],
        "Adaptation": [
            "I try to handle everything myself, even when it’s too much.",
            "I adjust to new situations, but it drains me.",
            "I take on more than I should because I don’t want to disappoint people.",
            "I get overwhelmed when too many expectations pile up.",
            "I hide my stress until I can’t anymore.",
            "I feel responsible for keeping things together.",
            "I adapt quickly, but it costs me energy.",
            "I feel guilty when I can’t keep up.",
            "I need downtime to recover after stressful days.",
            "I get overloaded when people expect too much from me."
        ]
    }

    results = {}

    for section, questions in sections.items():
        print(f"\n--- SECTION: {section.upper()} ---")
        total = 0
        for i, q in enumerate(questions, 1):
            while True:
                try:
                    val = int(input(f"{i}. {q} (1-5): "))
                    if 1 <= val <= 5:
                        total += val
                        break
                    else:
                        print("Please enter a number between 1 and 5.")
                except ValueError:
                    print("Invalid input. Please enter a digit.")
        
        # Scoring Logic
        if 10 <= total <= 23:
            label = f"{section[0]}F" # Flexed
        elif 24 <= total <= 37:
            label = f"{section[0]}S" # Sustained
        else:
            label = f"{section[0]}L" # Locked
            
        results[section] = {"score": total, "label": label}

    # Final Output
    profile = "-".join([res["label"] for res in results.values()])
    
    print("\n" + "="*60)
    print("FINAL IDENTITY PROFILE")
    print("="*60)
    for section, data in results.items():
        print(f"{section:10}: {data['score']} points -> {data['label']}")
    
    print("-"*60)
    print(f"YOUR HANDSHAKE STRING: {profile}")
    print("-"*60)
    print("Copy this string into your GitHub Contribution Handshake.")
    print("="*60)

if __name__ == "__main__":
    run_test()

