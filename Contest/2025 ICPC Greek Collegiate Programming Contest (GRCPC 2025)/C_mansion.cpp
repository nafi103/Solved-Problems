#include <bits/stdc++.h>
 using namespace std;
 #ifndef ONLINE_JUDGE
//#include "trace.cpp"
#else
#define dbg(...)
#endif
 int32_t main() {
  cin.tie(0) -> sync_with_stdio(0);
  int n, m;
  cin >> n >> m;
  vector<vector<pair<int, int>>> g(n);
  for (int i = 0; i < m; i++) {
    int u, v, w;
    cin >> u >> v >> w;
    --u, --v;
    g[u].push_back({v, w});
  }
  using pii = pair<int, int>;
  const int inf = 1e9;
  vector<int> dist(n, inf);
  dist[0] = 0;
  priority_queue<pii, vector<pii>, greater<pii>> q;
  q.push({0, 0});
  while (q.size()) {
    auto [w, v] = q.top(); q.pop();
    if (dist[v] != w) continue;
    for (auto &[u, wt] : g[v]) {
      if (dist[u] > dist[v] + wt) {
        dist[u] = dist[v] + wt;
        q.push({dist[u], u});
      }
    }
  }
  if (dist[n - 1] > inf / 2) dist[n - 1] = -1;
  cout << dist[n - 1];
  return 0;
}