# 形式手法+関数型プログラミング+AI駆動開発デモ

## プレゼンテーション情報

このプロジェクトは、**2025 FP祭り**でのプレゼンテーション「**AIと共に進化する開発手法：形式手法と関数型プログラミングの可能性**」のためのデモアプリケーションです。

- **イベント**: 2025 FP祭り
- **セッション**: [AIと共に進化する開発手法：形式手法と関数型プログラミングの可能性](https://fortee.jp/2025fp-matsuri/proposal/56b9175d-1468-4ab0-8063-180491bb16ed)
- **テーマ**: CursorやCline、DevinなどのAIエージェントを活用した開発における、形式手法や関数型プログラミングの価値実証

## プロジェクト概要

このプロジェクトは、**社内経費申請システム**を題材に、従来の開発手法と「形式手法 + 関数型プログラミング + AI駆動開発」の違いを実演するデモアプリケーションです。

### プレゼンテーションの背景
2025年現在、CursorやCline、DevinなどのAIエージェントを活用した開発が主流となりつつあります。しかし、大規模な開発においては、AIが実装しやすい「**枠組みの提供**」と「**コンテキストの最小化**」が重要となります。本デモでは、形式手法や関数型プログラミングの手法がこれらの課題にどのように寄与するかを、具体的な事例を通じて検証します。

### デモの目的
- **AIエージェント活用の最適化**: 形式手法による「枠組みの提供」でAIの実装精度向上
- **コンテキスト最小化の実証**: 関数型プログラミングによる副作用の分離と理解しやすいコード
- **開発生産性と品質の両立**: 上記手法とAI駆動開発の相乗効果による効率的で堅牢な開発プロセス
- **実践的価値の提示**: 聴衆が実際のプロジェクトで活用できる具体的なアプローチの提案

## アプリケーション仕様

### ドメイン: 社内経費申請システム

#### 基本エンティティ
- **経費申請 (Expense)**
    - ID, 申請者, 金額, 申請タイプ, 説明, 状態, 申請日時
    - 申請タイプ: 交通費, 宿泊費, 会議費, 備品購入

- **ユーザー (User)**
    - ID, 名前, メールアドレス, 役職, 上司

- **承認履歴 (ApprovalHistory)**
    - 承認者, 承認日時, アクション, コメント

#### 承認フロー仕様
```
金額による承認パス:
- 〜10,000円: 直属マネージャーのみ
- 10,001円〜50,000円: マネージャー → 部長
- 50,001円〜: マネージャー → 部長 → 経理部長
```

#### 状態遷移
```
Draft → Submitted → ManagerReview → [DirectorReview] → [FinanceReview] → Approved
                                                                     ↘ Rejected
                                                                       ↓
                                                                     Draft (修正後再申請)
```

#### ビジネス制約
1. **権限制約**
    - 申請者は自分の申請を承認できない
    - 承認は階層順序で実行（マネージャー承認前に部長は承認不可）
    - 上司のみが部下の申請を承認可能

2. **状態制約**
    - Draft状態でのみ編集可能
    - 承認済み申請は変更不可
    - 差し戻し時はコメント必須

3. **時間制約**
    - 72時間無応答で自動エスカレーション
    - 承認期限: 申請から2週間以内

## 技術スタック

### 形式手法
- **TLA+**: ワークフロー状態遷移の仕様記述・検証
- **Alloy**: 制約条件・権限モデルの検証
- **契約による設計**: 実装レベルでの事前条件・事後条件

### バックエンド
- **Kotlin + Spring Boot**
- **Arrow-kt**: 関数型プログラミングライブラリ
- **PostgreSQL**: データベース
- **Gradle**: ビルドツール

### フロントエンド
- **React + TypeScript**
- **fp-ts**: 関数型プログラミングライブラリ
- **Vite**: ビルドツール
- **Axios**: HTTP クライアント

## プロジェクト構造

```
/
├── README.md                           # このインストラクションドキュメント
├── docs/                              # ドキュメント
│   ├── presentation-context.md         # プレゼンテーション詳細情報
│   ├── demo-script.md                 # 実際のデモ進行台本
│   ├── legacy-spec.md                 # 問題のある従来仕様（Phase 1）
│   └── formal-specification.md        # 形式手法による改善仕様（Phase 1）
├── formal-specs/                      # 形式手法仕様（Phase 1）
│   ├── workflow.tla                   # TLA+によるワークフロー仕様
│   ├── constraints.als               # Alloyによる制約モデル
│   └── verification-results/         # 検証結果とレポート
├── legacy-demo/                       # 従来手法のデモ実装（問題のある例）
│   ├── frontend-ts-legacy/            # 従来のTypeScript実装（問題のある例）
│   │   ├── package.json
│   │   ├── src/
│   │   │   ├── expense-form.ts
│   │   │   ├── approval-logic.ts
│   │   │   └── state-management.ts
│   │   └── demo-bugs.md              # 意図的に含まれたバグの説明
│   └── backend-kotlin-legacy/         # 従来のKotlin実装（問題のある例）
│       ├── build.gradle.kts
│       ├── src/main/kotlin/
│       │   └── com/legacy/expense/
│       │       ├── ExpenseController.kt
│       │       ├── ExpenseService.kt
│       │       ├── ExpenseEntity.kt
│       │       └── ExpenseRepository.kt
│       └── known-issues.md           # 既知の問題の説明
├── functional-demo/                   # 関数型+形式手法のデモ実装
│   ├── backend-kotlin/               # Kotlin + Arrow-kt実装
│   │   ├── build.gradle.kts
│   │   ├── src/main/kotlin/
│   │   │   └── com/demo/expense/
│   │   │       ├── domain/           # ドメインモデル
│   │   │       │   ├── ExpenseState.kt
│   │   │       │   ├── ApprovalPath.kt
│   │   │       │   └── BusinessRule.kt
│   │   │       ├── application/      # アプリケーション層
│   │   │       │   ├── ExpenseService.kt
│   │   │       │   └── WorkflowEngine.kt
│   │   │       ├── infrastructure/   # インフラ層
│   │   │       │   ├── repository/
│   │   │       │   └── config/
│   │   │       └── api/             # API層
│   │   │           ├── ExpenseController.kt
│   │   │           └── dto/
│   │   └── src/test/kotlin/         # テスト
│   └── frontend-react/              # React + TypeScript + fp-ts実装
│       ├── package.json
│       ├── src/
│       │   ├── types/               # 型定義
│       │   │   ├── ExpenseTypes.ts
│       │   │   ├── UserTypes.ts
│       │   │   └── ApiTypes.ts
│       │   ├── components/          # コンポーネント
│       │   │   ├── ExpenseForm.tsx
│       │   │   ├── ApprovalFlow.tsx
│       │   │   └── ExpenseList.tsx
│       │   ├── state/              # 状態管理
│       │   │   ├── ExpenseState.ts
│       │   │   └── reducers/
│       │   ├── api/                # API通信
│       │   │   ├── ExpenseApi.ts
│       │   │   └── types/
│       │   └── utils/              # ユーティリティ
│       └── src/test/               # テスト
├── ai-generation/                     # AI駆動開発の成果物（Phase 4）
│   ├── generated-code/               # AIが生成したコード
│   ├── prompts-used.md              # 使用したプロンプトの記録
│   ├── generation-results.md        # 生成結果の評価
│   └── test-cases/                  # AIが生成したテストケース
└── presentation/                     # プレゼンテーション素材（Phase 5）
    ├── slides/                      # スライド資料
    ├── demo-data/                   # デモ用サンプルデータ
    ├── live-coding-scripts/         # ライブコーディング用スクリプト
    └── comparison-charts/           # ビフォー/アフター比較資料
```

## 開発フェーズ

### Phase 1: 形式手法による仕様策定
**目標**: バグを含む従来仕様と、形式手法で厳密化した仕様の対比

#### 1.1 問題のある従来仕様の作成
- [x] `docs/legacy-spec.md` - 曖昧で不完全な仕様書を作成
- [x] `legacy-demo/frontend-ts-legacy/` - 従来のTypeScript実装例（問題のあるパターン）
- [x] `legacy-demo/backend-kotlin-legacy/` - 従来のKotlin実装例（問題のあるパターン）

#### 1.2 TLA+による状態遷移仕様
- [x] `formal-specs/workflow.tla` - 経費申請ワークフローの状態遷移
- [ ] `formal-specs/verification-results/` - 状態遷移図の生成とモデル検査の実行
- [ ] 不正な遷移パスの検出と修正

#### 1.3 Alloyによる制約モデリング
- [x] `formal-specs/constraints.als` - 権限制約と金額ルールのモデル
- [ ] 制約違反パターンの自動検出
- [ ] 反例の分析と仕様の改善

#### 1.4 統合仕様書の作成
- [x] `docs/formal-specification.md` - TLA+/Alloyを統合した完全仕様

### Phase 2: 関数型バックエンド実装
**目標**: 型安全で副作用を排除した堅牢な実装

#### 2.1 プロジェクト初期設定
- [ ] `functional-demo/backend-kotlin/` - Spring Boot + Kotlin プロジェクト作成
- [ ] Arrow-kt 依存関係追加
- [ ] データベース設定 (PostgreSQL)

#### 2.2 ドメインモデル設計
- [ ] `functional-demo/backend-kotlin/src/main/kotlin/domain/` - sealed class による状態モデリング
- [ ] `ExpenseState.kt` - 状態遷移の型安全な表現
- [ ] `ApprovalPath.kt` - 承認パスの型定義
- [ ] `BusinessRule.kt` - ビジネスルールの純粋関数実装

#### 2.3 インフラストラクチャ層
- [ ] `functional-demo/backend-kotlin/src/main/kotlin/infrastructure/repository/` - データアクセス層
- [ ] Either型を使った安全なデータ操作
- [ ] 不変データ構造での永続化

#### 2.4 アプリケーション層
- [ ] `functional-demo/backend-kotlin/src/main/kotlin/application/` - ビジネスロジック層
- [ ] 純粋関数でのワークフロー処理
- [ ] 副作用の分離と制御

#### 2.5 API層
- [ ] `functional-demo/backend-kotlin/src/main/kotlin/api/` - REST API実装
- [ ] 型安全なリクエスト/レスポンス処理
- [ ] エラーハンドリングの統一

### Phase 3: 関数型フロントエンド実装
**目標**: 型安全で予測可能なUIの実装

#### 3.1 プロジェクト初期設定
- [ ] `functional-demo/frontend-react/` - React + TypeScript + Vite プロジェクト作成
- [ ] fp-ts 依存関係追加
- [ ] 開発環境の構築

#### 3.2 型定義とデータモデル
- [ ] `functional-demo/frontend-react/src/types/` - バックエンドと対応する型定義
- [ ] `ExpenseTypes.ts` - 経費申請関連の型
- [ ] `UserTypes.ts` - ユーザー関連の型
- [ ] `ApiTypes.ts` - API通信の型

#### 3.3 状態管理
- [ ] `functional-demo/frontend-react/src/state/` - 関数型状態管理
- [ ] Option/Either型を使った安全な状態操作
- [ ] 不変データ構造での状態更新

#### 3.4 コンポーネント実装
- [ ] `functional-demo/frontend-react/src/components/` - 純粋関数コンポーネント
- [ ] `ExpenseForm.tsx` - 経費申請フォーム
- [ ] `ApprovalFlow.tsx` - 承認フロー表示
- [ ] `ExpenseList.tsx` - 申請一覧

#### 3.5 API通信
- [ ] `functional-demo/frontend-react/src/api/` - 型安全なAPI通信
- [ ] Task型を使った非同期処理
- [ ] エラー処理の統一

### Phase 4: AI駆動開発の実証
**目標**: AIを活用した効率的な開発プロセスの実演

#### 4.1 仕様からコード生成
- [ ] `ai-generation/generated-code/` - TLA+仕様からKotlinの型定義生成
- [ ] Alloy制約からバリデーション関数生成
- [ ] `ai-generation/generation-results.md` - 生成コードの品質評価

#### 4.2 テスト自動生成
- [ ] `ai-generation/test-cases/` - 形式仕様からテストケース生成
- [ ] 境界値テストの自動作成
- [ ] プロパティベーステストの実装

#### 4.3 リファクタリング支援
- [ ] 命令型コードから関数型への変換
- [ ] `ai-generation/prompts-used.md` - 使用したプロンプトの記録
- [ ] 継続的改善のワークフロー

### Phase 5: デモ用実装
**目標**: プレゼンテーション用の実演可能なアプリケーション

#### 5.1 比較デモの準備
- [ ] `legacy-demo/demo-bugs.md` - 従来実装の問題点の整理
- [ ] `functional-demo/` - 改善された実装の最終調整
- [ ] `presentation/demo-data/` - 対比デモ用のサンプルデータ

#### 5.2 プレゼンテーション素材
- [ ] `presentation/slides/` - デモ用スライド資料
- [ ] `presentation/comparison-charts/` - ビフォー/アフターの比較資料
- [ ] `presentation/live-coding-scripts/` - ライブコーディング用スクリプト

#### 5.3 実行環境の準備
- [ ] Docker compose による統合環境
- [ ] デモ実行用のMakefileまたはスクリプト
- [ ] プレゼンテーション用のREADME

## AI駆動開発での重要なプロンプト

### 仕様理解のプロンプト
```
以下の経費申請システムの要件から、型安全なKotlinの sealed class で状態遷移を表現してください。
また、各状態遷移で必要な事前条件・事後条件も契約として実装してください。

[要件を貼り付け]
```

### テスト生成のプロンプト
```
以下のAlloy制約仕様から、Kotlinのテストケースを生成してください。
特に境界値、エラーケース、権限チェックのテストを重点的にお願いします。

[Alloy仕様を貼り付け]
```

### リファクタリングのプロンプト
```
以下の命令型JavaScriptコードを、TypeScript + fp-ts を使って関数型にリファクタリングしてください。
エラーハンドリングはEither型、null安全性はOption型を使用してください。

[コードを貼り付け]
```

## 成果物の評価基準

### 品質指標
- **型安全性**: コンパイル時エラー検出率
- **保守性**: 循環複雑度とテストカバレッジ
- **信頼性**: 形式検証で検出されたバグ数
- **開発効率**: AI支援によるコード生成率

### デモ効果の測定
- **理解度**: 聴衆へのアンケート結果
- **印象度**: ビフォー/アフターの差異認識
- **実用性**: 実際のプロジェクトへの適用意向

## 開発の進め方

1. **各フェーズを順次実行**し、前フェーズの成果物を次フェーズで活用
2. **AI（Claude Code）との対話**を通じて、仕様の曖昧さを解消
3. **継続的な検証**により、形式手法の効果を定量的に測定
4. **デモ用資料の並行作成**で、技術的成果をプレゼンテーション可能な形に

## 次のステップ

このドキュメントを元に、以下の順序で開発を進めてください：

1. `docs/legacy-spec.md` の作成（問題のある仕様書）
2. `formal-specs/workflow.tla` の作成（TLA+仕様）
3. `formal-specs/constraints.als` の作成（Alloy仕様）
4. バックエンド実装の開始
5. フロントエンド実装の開始

各ステップで不明な点があれば、このドキュメントを参照しながら段階的に進めてください。