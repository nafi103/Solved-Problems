 #include <bits/stdc++.h>
 #define ll long long
 #define int int64_t
 using namespace std;
  int32_t main() {
  ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
  int n;
  cin >> n;
  int arr[n][n];
  for (int i = 0; i < n; i++) {
   for (int j = 0; j < n; j++)
    cin >> arr[i][j];
  }
  for (int mid = 0; mid < n; mid++) {
   for (int i = 0; i < n; i++) {
    if (i == mid)
     continue;
    for (int j = i + 1; j < n; j++)
     if (j == i || j == mid)
      continue;
     else if (arr[i][mid]+arr[mid][j] < arr[i][j]) {
      cout << "-1\n";
      return 0;
     }
   }
  }
  ll ans = 0;
  for (int mid = 0; mid < n; mid++) {
   for (int i = 0; i < n; i++) {
    if (i == mid)
     continue;
    for (int j = i + 1; j < n; j++)
     if (j == i || j == mid)
      continue;
     else if (arr[i][mid]+arr[mid][j] == arr[i][j]) {
      // cout << i << " " << j << " " << mid << endl;
      arr[i][j]=INT_MAX, ans++;
     }
   }
  }
  cout << ans << '\n';
 }