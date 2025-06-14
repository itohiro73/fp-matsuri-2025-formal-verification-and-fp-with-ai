State = {LoginScreen, MainScreen, ErrorScreen}
Input = {LoginButton, CancelButton, BackButton}

Transition(LoginScreen, LoginButton) →
  IF validCredentials THEN MainScreen ELSE ErrorScreen


  // 基本的な構造定義
  sig Employee {
      employeeId: EmployeeId,
      department: Department,
      manager: lone Employee  // lone = 0個または1個
  }

  sig ExpenseReport {
      id: ReportId,
      submitter: Employee,
      items: set ExpenseItem,  // set = 複数の関連
      status: one ReportStatus,
      approvals: set Approval
  }

  abstract sig ReportStatus {}
  one sig Draft, Submitted, UnderReview, Approved, Rejected extends ReportStatus {}

  // 制約の定義（ビジネスルール）
  fact ValidManagerHierarchy {
      // 管理者の循環参照を禁止
      no e: Employee | e in e.^manager
      // ^は推移的閉包（transitive closure）
  }

  fact ReportStatusConsistency {
      // 承認済みレポートには承認記録が必要
      all r: ExpenseReport {
          r.status = Approved implies some r.approvals
          r.status = Draft implies no r.approvals
      }
  }

// 検証したいプロパティ
pred NoOrphanedReports {
  // すべてのレポートに有効な提出者がいる
  all r: ExpenseReport | some e: Employee | r.submitter = e
}

// Alloy Analyzerによる検証コマンド
check NoOrphanedReports for 5  // 最大5個のオブジェクトで検証
run ShowValidConfiguration for 3  // 有効な設定例を3個まで生成