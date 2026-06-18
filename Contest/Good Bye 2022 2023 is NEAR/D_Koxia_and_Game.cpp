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
 const int N = 2e5 + 10;
vector<vector<int>> g(N);
int n, vertex, edges, self_loop, a[N];
bool visited[N];
 void input(){
 cin >> n;
 for(int i = 0; i < n; i++){
  cin >> a[i];
  visited[i + 1] = false;
  g[i + 1].clear();
 }
 for(int i = 0, u, v = a[0]; i < n; i++, v = a[i]){
  cin >> u;
  g[u].push_back(v);
  g[v].push_back(u);
 }
}
 void dfs(int node){
 visited[node] = true;
 vertex++;
 for(auto &adj: g[node]){
  edges++;
  if(!visited[adj])
   dfs(adj);
  if(node == adj)
   self_loop++;
 }
}
 void solve()
{
 input();
 int ans = 1;
 for(int i = 1; i <= n; i++){
  if(!visited[i]){
   vertex = edges = self_loop = 0;
   dfs(i);
   if(edges != 2 * vertex){
    ans = 0;
    break;
   }else if(self_loop)
    ans = (ans * n) % mod;
   else
    ans = (ans << 1) % mod;
  }
 }
 cout << ans << endl;
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