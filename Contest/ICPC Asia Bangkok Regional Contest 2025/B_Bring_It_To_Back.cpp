#include <bits/stdc++.h>
 using namespace std;
 #ifndef ONLINE_JUDGE
#include "trace.cpp"
#else
#define dbg(...)
#endif
 #define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define make_unique(x) sort(all((x))); (x).erase(unique(all((x))), (x).end())
#define take_graph(m) for (int i = 0, u, v; i < m; i++) {cin >> u >> v; --u, --v; g[u].push_back(v); g[v].push_back(u);}
#define take_vec(a) for (auto &x : a) cin >> x; 
#define int int64_t
 /*
    n = 4, m = 4 
    ?
    4 3 2 1
    4 3 1 2
    4 1 2 3
    1 2 3 4
    1 2 4 3
    1 2 3 4
    m = 5?
     m = 6?
    1 2 3 4
     4 3 2 1
     ...3
    1 2 3 4
    1 
     1 2 3
     m = 1
    3 1 2
    m = 2
     3 2 1
     m = 3?
    3 2 1
    2 1 3
  */
 void solve() {
  int n;
  cin >> n;
  int m;
  cin >> m;
   if (n == 1) {
    cout << "1\n";
    return;
  }
   if (n == 2) {
    if (m & 1) {
      cout << "2 1\n";
      return;
    } else {
      cout << "1 2\n";
      return;
    }
  }
   deque<int> a(n);
  iota(all(a), 1);  
  if (m < n) {
    reverse(all(a));
    reverse(a.begin() + m, a.end());
  } else {
    reverse(all(a));
  }
  for (int i = 0; i < n; i++) {
    cout << a[i] << " \n"[i == n - 1];
  }
}
 int32_t main() {
  cin.tie(0) -> sync_with_stdio(0);
  int t; cin >> t;
  while (t--) solve();
  return 0;
}