#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 struct DSU{
 int n;
 vector<int> parent, _size;
  DSU(int _n){
  n = _n;
  parent.resize(n);
  _size.assign(n, 1);
  iota(all(parent), 0);
 }
  int find(int node){
  if(parent[node] == node)
   return node;
  return parent[node] = find(parent[node]);
 }
  void Union(int a, int b){
  a = find(a);
  b = find(b);
  if(a == b)
   return;
  if(_size[a] > _size[b])
   swap(a, b);
  parent[a] = b;
  _size[b] += _size[a];
 }
};
 void solve()
{
    int n, m, k;
    cin >> n >> m >> k;
    vector<array<int, 3>> edges;
    DSU uf(n);
    for(int i = 0, u, v, w; i < m; i++){
     cin >> u >> v >> w;
     u--, v--;
     edges.push_back({w, u, v});
    }
    sort(all(edges));
    vector<int> dismissed, taken;
    for(auto &[w, u, v]: edges){
     if(uf.find(u) != uf.find(v)){
      taken.push_back(w);
      uf.Union(u, v);
     }else{
      dismissed.push_back(w);
     }
    }
    int cost = 0;
    if(taken.back() < k){
     cost = k - taken.back();
     for(auto &x: dismissed){
      cost = min(cost, abs(x - k));
     }
    }else{
     while(!taken.empty() and taken.back() > k){
      cost += taken.back() - k;
      taken.pop_back();
     }
    }
    cout << cost << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}