# 形式手法検証環境

このディレクトリには、経費申請システムの形式仕様と検証環境が含まれています。

## 概要

- **TLA+**: ワークフローの状態遷移仕様
- **Alloy**: ビジネスルールと制約の仕様
- **Docker**: 検証ツールの実行環境
- **CI/CD**: GitHub Actionsによる自動検証

## ファイル構成

```
formal-specs/
├── workflow.tla          # TLA+による状態遷移仕様
├── workflow.cfg          # TLA+モデル検査設定
├── constraints.als       # Alloyによる制約仕様
├── Dockerfile           # 検証ツール環境
├── docker-compose.yml   # Docker構成
├── Makefile            # ビルド・検証タスク
├── verify.sh           # 検証実行スクリプト
└── verification-results/ # 検証結果出力ディレクトリ
```

## クイックスタート

### ローカル環境での検証

#### 方法1: Dockerを使用（推奨）

```bash
# Docker環境のビルド
make docker-build

# 検証の実行
make docker-verify
```

#### 方法2: ローカルツールを使用

必要なツール:
- Java 11以上
- TLA+ tools (tla2tools.jar)
- Alloy (alloy.jar)

```bash
# すべての検証を実行
make verify

# TLA+のみ検証
make verify-tla

# Alloyのみ検証
make verify-alloy
```

### CI環境での検証

GitHub Actionsが自動的に以下を実行:
1. formal-specs/配下の変更を検出
2. TLA+モデル検査を実行
3. Alloy構文検証を実行
4. 結果をアーティファクトとして保存

## 検証内容

### TLA+ (workflow.tla)

**不変条件 (Invariants)**:
- `TypeOK`: 型の整合性
- `NoSelfApproval`: 自己承認の禁止
- `SequentialApproval`: 順序承認の保証
- `OnlyAuthorizedApprovers`: 権限承認の保証

**プロパティ (Properties)**:
- `ExpenseEventuallyProcessed`: 申請の最終処理保証

### Alloy (constraints.als)

**アサーション (Assertions)**:
- `NoSelfApprovalAssertion`: 自己承認禁止の検証
- `ApprovalHierarchyAssertion`: 承認階層の検証
- `AmountBasedRulesAssertion`: 金額ベースルールの検証

**述語 (Predicates)**:
- `systemInvariants`: システム不変条件の検証

## 検証結果の確認

検証後、`verification-results/`ディレクトリに結果が出力されます:

```
verification-results/
├── tla/
│   ├── tlc-output.log      # TLA+検証ログ
│   └── coverage.txt        # カバレッジ情報
├── alloy/
│   └── alloy-output.log    # Alloy検証ログ
└── verification-report.md  # 統合レポート
```

## トラブルシューティング

### TLA+エラー: "Out of memory"
```bash
# メモリを増やして実行
java -Xmx4G -cp tla2tools.jar tlc2.TLC -config workflow.cfg workflow.tla
```

### Alloy: GUI表示エラー
Alloyは完全な分析にGUIが必要です。CI環境では構文検証のみ実行されます。

### Docker: ビルドエラー
```bash
# キャッシュをクリアして再ビルド
docker-compose build --no-cache
```

## 開発ガイド

### 新しい制約の追加

1. **TLA+**: `workflow.tla`に新しい不変条件を追加
2. **Alloy**: `constraints.als`に新しいfactまたはassertionを追加
3. **設定更新**: 必要に応じて`workflow.cfg`を更新
4. **検証実行**: `make verify`で検証

### 検証の拡張

1. `verify.sh`に新しい検証ステップを追加
2. `Makefile`に新しいターゲットを追加
3. `.github/workflows/formal-verification.yml`を更新

## 参考資料

- [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)
- [Alloy Documentation](http://alloytools.org/documentation.html)
- [TLC Model Checker Guide](https://learntla.com/topics/tlc/)

## ライセンス

このプロジェクトのライセンスに従います。