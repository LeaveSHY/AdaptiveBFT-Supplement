This repository contains the complete security analysis and TLA+ formal verification of **AdaptiveBFT** protocol.

# AdaptiveBFT Formal Verification

The formal specifications and verification models for **AdaptiveBFT** are ready.
It utilizes **TLA+** to model the protocol's core logic, focusing on its two novel mechanisms:
1.  **Adaptive View-Change (AVC)**: A reputation-based leader election mechanism (RVS).
2.  **Adaptive Pipeline Scheduling (APS)**: A dynamic parameter reconfiguration scheduler.

The repository verifies **Safety** (Consistency) and **Liveness** (Chain Growth) under various adversarial conditions, including adaptive leader corruption and high-frequency parameter oscillation.

---

## 📂 Repository Structure

```text
AdaptiveBFT-Verification/
├── Makefile                        # Automation for running tests
├── run.sh                          # Helper script for setting TLA+ paths
├── specifications/                 # Core Protocol Specifications
│   ├── AdaptiveBFT.tla             # [Main] Consensus flow integrating AVC & APS (Algo 6)
│   ├── AdaptiveBFT_Types.tla       # Data structures (Message, Block, QC)
│   └── modules/
│       ├── AVC_RVS.tla             # Reputation & VRF Sortition Logic (Algo 1 & 2)
│       ├── APS_Scheduler.tla       # Dynamic Scheduling Logic (Algo 5)
│       └── Mempool.tla             # Pre-validation & Priority Queue (Algo 3 & 4)
└── models/                         # Model Checking Scenarios (Tests)
    ├── MC_AdaptiveAttack.tla/.cfg  # Scenario 1: Adaptive Primary Corruption
    └── MC_LivenessAPS.tla/.cfg     # Scenario 2: Dynamic Reconfiguration Safety
```

## 🛠 Prerequisites
* **Java Runtime Environment (JRE)**: Version 11 or higher.
* **TLA+ Tools**: Download `tla2tools.jar` from [TLA+ Releases](https://github.com/tlaplus/tlaplus/releases) and place it in the root directory of this repository.

## 🚀 How to Run Verification
You can use `make` for automated testing or run specific scripts directly.

### Option 1: Using Make (Recommended)
Run all verification tests:
```bash
make all
```

Run specific scenarios:
```bash
make test-attack   # Verify AVC Security
make test-aps      # Verify APS Safety
```

Clean up temporary files:
```bash
make clean
```

### Option 2: Using Shell Script
First, ensure the script is executable:
```bash
chmod +x run.sh
```

Then run:
```bash
./run.sh attack   # Scenario 1
./run.sh aps      # Scenario 2
```

## 🧪 Verification Scenarios

### 1. Adaptive Primary Corruption Test (`MC_AdaptiveAttack`)
* **Goal**: Verify **Liveness** and **AVC Robustness**.
* **Adversary**: An adaptive adversary that monitors the network. Once a leader issues a proposal, the adversary immediately launches a DoS attack (forcing a timeout) to halt consensus.
* **Success Criteria**: The model checks `LivenessUnderAttack`. It proves that despite targeted attacks, the **RVS (Reputation-based Verifiable Sortition)** mechanism eventually selects a leader that the adversary cannot predict or corrupt within its budget, allowing the chain to grow.

### 2. APS Reconfiguration Safety Test (`MC_LivenessAPS`)
* **Goal**: Verify **Safety** under dynamic reconfiguration.
* **Scenario**: The system undergoes high-frequency changes in critical parameters (e.g., `BatchSize`, `PipelineDepth`, `Timeout`) due to unstable network conditions.
* **Success Criteria**: The model checks `ReconfigurationSafety`. It proves that "hot swapping" configuration parameters in the middle of a consensus view does not lead to state divergence (split-brain) or protocol deadlock.

## 📄 Mapping to Paper

| Component | Paper Section | Specification File |
| :--- | :--- | :--- |
| **Data Structures** | Sec 4.1 | `specifications/AdaptiveBFT_Types.tla` |
| **RVS & AVC** | Algo 1 & 2 | `specifications/modules/AVC_RVS.tla` |
| **Pre-Validation** | Algo 3 | `specifications/modules/Mempool.tla` |
| **Priority Queue** | Algo 4 | `specifications/modules/Mempool.tla` |
| **APS Scheduler** | Algo 5 | `specifications/modules/APS_Scheduler.tla` |
| **Consensus Process** | Algo 6 | `specifications/AdaptiveBFT.tla` |


## Citation

```bibtex
@misc{AdaptiveBFT2026,
      title={AdaptiveBFT: Achieving Dual-Adaptability for Pipelined Consensus in Large-Scale Networks}, 
      author={Liang Wang and Liangmin Wang and Xia Feng and Haiqin Wu and Boris Düdder and Lu Liu},
      year={2026},
      publisher = {GitHub},
      howpublished = {\url{https://anonymous.4open.science/r/AdaptiveBFT-Supplement-TON}},
}
```

## License
MIT License.
