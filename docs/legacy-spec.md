# 経費申請システム仕様書（従来版）

## 1. 概要

社内経費申請システムは、従業員が交通費、宿泊費、会議費、備品購入などの経費申請を行い、マネージャーや部長などの上司が承認を行うシステムです。

## 2. 基本機能

### 2.1 経費申請機能
- 従業員は経費申請を作成できる
- 申請項目：申請者、金額、申請タイプ、説明
- 申請後は承認待ち状態になる

### 2.2 承認機能
- 上司は部下の申請を承認または拒否できる
- 承認には階層がある
- 金額により承認者が変わる

## 3. 承認フロー

### 3.1 金額別承認ルール
- 少額（10,000円以下）：直属マネージャーが承認
- 中額（10,001円〜50,000円）：マネージャー承認後、部長承認
- 高額（50,001円以上）：マネージャー、部長、経理部長の順で承認

### 3.2 状態遷移
申請は以下の状態を遷移する：
1. 下書き
2. 申請済み
3. マネージャー承認待ち
4. 部長承認待ち（必要な場合）
5. 経理部長承認待ち（必要な場合）
6. 承認済み
7. 拒否

## 4. ビジネスルール

### 4.1 権限ルール
- 申請者は自分の申請を承認できない
- 上司のみが部下の申請を承認できる
- 承認は順序通り行う必要がある

### 4.2 時間制限
- 承認者が72時間以内に対応しない場合、自動的に次の階層にエスカレーションする
- 申請から2週間以内に最終承認が必要

### 4.3 編集ルール
- 承認済みの申請は編集できない
- 拒否された申請は修正して再申請可能

## 5. データ構造

### 5.1 経費申請エンティティ
```
Expense {
  id: 数値
  申請者: 文字列
  金額: 数値
  タイプ: 文字列（交通費、宿泊費、会議費、備品購入）
  説明: 文字列
  状態: 文字列
  申請日: 日付
}
```

### 5.2 ユーザーエンティティ
```
User {
  id: 数値
  名前: 文字列
  メール: 文字列
  役職: 文字列
  上司: 数値（上司のユーザーID）
}
```

### 5.3 承認履歴エンティティ
```
ApprovalHistory {
  承認者: 数値
  承認日: 日付
  アクション: 文字列（承認、拒否）
  コメント: 文字列
}
```

## 6. システム要件

### 6.1 パフォーマンス
- 申請一覧表示は3秒以内
- 承認処理は1秒以内

### 6.2 セキュリティ
- ユーザー認証が必要
- 他人の申請は見れない
- 管理者は全申請を確認可能

### 6.3 可用性
- 平日9:00-18:00は99%の稼働率
- メンテナンス時間は事前通知

## 7. 注意事項

- 申請金額に上限はない
- 承認者が不在の場合の代理承認は今後検討
- 外貨での申請は円換算で処理
- 申請の取り消しは承認前のみ可能

---

## 8. 仕様書の意図的な問題点の解説

**注記**: この仕様書は従来の開発手法による例であり、意図的に曖昧さや不完全な部分を含んでいます。形式手法による改善版と比較するためのサンプルです。

### 8.1 曖昧性の問題

#### 8.1.1 状態遷移の曖昧さ
- **問題**: 「申請済み」から「マネージャー承認待ち」への遷移条件が不明確
- **影響**: どのタイミングで状態が変わるのか実装者により解釈が分かれる
- **例**: 申請ボタンを押した瞬間なのか、バリデーション通過後なのか不明

#### 8.1.2 承認順序の曖昧さ
- **問題**: 「順序通り行う必要がある」の具体的な制約が不明
- **影響**: 飛び越し承認や並行承認を防げるかどうか不明確
- **例**: 部長が先にアクセスした場合の動作が未定義

#### 8.1.3 エスカレーション条件の曖昧さ
- **問題**: 「72時間以内に対応しない場合」の「対応」の定義が不明
- **影響**: システムアクセスだけで「対応」とするのか、実際の承認/拒否が必要なのか不明
- **例**: 承認者がログインしただけでタイマーがリセットされるのか不明

### 8.2 不完全性の問題

#### 8.2.1 例外処理の欠如
- **問題**: 承認者が退職した場合の処理が未定義
- **影響**: システムがデッドロック状態になる可能性
- **例**: 承認待ちの申請が永続的に処理されない状況

#### 8.2.2 並行性の考慮不足
- **問題**: 複数の承認者が同時にアクションする場合の動作が未定義
- **影響**: データの不整合や重複処理の可能性
- **例**: 二重承認や競合状態の発生

#### 8.2.3 データ整合性ルールの欠如
- **問題**: 申請金額の負数チェックや必須項目の制約が不明
- **影響**: 不正なデータの登録を防げない
- **例**: マイナス金額の申請や空の説明での申請

#### 8.2.4 権限チェックの詳細不足
- **問題**: 「上司のみが部下の申請を承認できる」の組織階層の定義が不明
- **影響**: 複雑な組織構造での動作が予測不能
- **例**: マトリックス組織や兼任役職での承認権限

### 8.3 一貫性の問題

#### 8.3.1 用語の不統一
- **問題**: 「マネージャー」「上司」「直属マネージャー」が混在
- **影響**: 同じ概念なのか違う概念なのか判断困難
- **例**: システム設計時に異なるエンティティとして実装される可能性

#### 8.3.2 データ型の曖昧さ
- **問題**: 「数値」「文字列」の具体的な制約が不明
- **影響**: 実装時にデータ長や精度の判断に迷う
- **例**: 金額フィールドの小数点処理や最大桁数

### 8.4 完全性の問題

#### 8.4.1 業務フローの抜け漏れ
- **問題**: 申請の修正・削除フローが不完全
- **影響**: 実際の業務で必要な操作が実装されない
- **例**: 承認済み申請の修正が必要になった場合の処理

#### 8.4.2 監査要件の欠如
- **問題**: 操作ログや証跡管理の要件が未記載
- **影響**: コンプライアンス要件を満たせない
- **例**: 「誰がいつ何を変更したか」の追跡ができない

### 8.5 形式手法による改善のポイント

これらの問題は **docs/formal-specification.md** の形式手法版で以下のように解決されています：

1. **TLA+による状態遷移の厳密定義** → 曖昧性の排除
2. **Alloy による制約の形式化** → 不完全性の解消  
3. **型安全性の保証** → データ整合性の確保
4. **不変条件の明示** → システムの健全性保証

この対比により、従来手法の限界と形式手法の有効性を具体的に示しています。