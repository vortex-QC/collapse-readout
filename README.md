# collapse-readout · 叠置裂解读出核

**Superposition–collapse readout core: four zero-sorry Lean theorems on Diffuse (atomless) measures.**

叠置裂解 = 叠置态 (结构面·群体性之源) × 裂解 (事件面·个体性之源) × 读数 (产物面) 的事件结构命题。
随机 = 两件的张力: **个体不可取出 (单点零测) × 群体确定 (测度结构给定)**。

## 内容 (Contents)

| 文件 | 内容 |
|---|---|
| `lean/SuperpositionMeasure.lean` | 地基: Diffuse (弥散) 测度定义 + 四件 (T_S1b / T_F1′-1 / T_F1′-2 / S-4, 含可数集零测) |
| `lean/CollapseReadout.lean` | R 系四件 (依赖 SuperpositionMeasure): |

- **R-1 `collapse_atoms`** — 可数读出集被单点原子族承载 (`ν s ≤ ∑' ν {f i}`): 测量史=原子堆积;
- **R-2 `guess_missed`** — Diffuse 测度下可数猜测集的补集满测 (`ν sᶜ = ν univ`): 猜中测度为零, 读数几乎必然在猜测之外;
- **R-3 `collapse_traceless`** — 取出单点实现不改群体测度 (`ν (insert x s) = ν s`): 裂解只产生实现不改测度;
- **R-4 `collapse_marginal`** — 二次裂解的第一边缘=单次裂解分布 (`map Prod.fst (ν.prod ν) = ν`): 裂解不产生新分布 (iid 边缘面)。

## 验证 (Verification)

- 2026-10-11 复验: `lake env lean DensityMath/CollapseReadout.lean` exit=0, 零 error, 两文件零 sorry;
- 四件 `#print axioms` = `[propext, Classical.choice, Quot.sound]` 标准三件套;
- 全库 build 8736 jobs 绿 (2026-10-10, 随录)。

## 状态 (Status)

内部理论交汇件的登记面 (registration of a convergent-line proposition; 零新公理, 零新增物理宣称)。
Companion package (候发布轮, Zenodo record pending)。
License: Code MIT / Docs CC-BY-4.0。
