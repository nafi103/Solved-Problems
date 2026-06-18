#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
// #define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void query1(int i){
 cout << "+ " << i << endl;
 cin >> i;
}
 int query2(int i, int j){
 cout << "? " << i << " " << j << endl;
 cin >> i;
 return i;
}
 void solve()
{
    int n;
    cin >> n;
    if(n == 1){
     cout << "! 1 1" << endl;
     cin >> n;
     return;
    }
    if(n == 2){
     cout << "! 1 2 2 1" << endl;
     cin >> n;
     return;
    }
    query1(n + 1);
    query1(n + 2);
    vector<vector<int>> t(n + 1);
    {
     int u = 1, v = n;
     while(u < v){
      t[u].push_back(v);
      t[v].push_back(u);
      u++, v--;
     }
     u = 2, v = n;
     while(u < v){
      t[u].push_back(v);
      t[v].push_back(u);
      u++, v--;
     }
    }
    vector<bool> visited(n + 1, false);
    int node = 1, cnt = n;
    vector<int> path = {0};
    path.reserve(n + 1);
    while(cnt--){
     visited[node] = true;
     path.push_back(node);
     for(auto &adj: t[node]){
      if(!visited[adj]){
       node = adj;
       break;
      }
     }
    }
    vector<int> pos(n + 1);
    for(int i = 1; i <= n; i++){
     pos[path[i]] = i;
    }
    int choose = 1, d = 0;
    for(int i = 2; i <= n; i++){
     int dis = query2(1, i);
     if(dis >= d){
      choose = i;
      d = dis;
     }
    }
    vector<int> ans1(n + 1), ans2(n + 1);
    ans1[choose] = path[1];
    ans2[choose] = path[n];
    for(int j = choose - 1; j >= 1; j--){
     int dis = query2(choose, j);
     ans1[j] = path[dis + 1];
     ans2[j] = path[n - dis];
    }
    for(int j = choose + 1; j <= n; j++){
     int dis = query2(choose, j);
     ans1[j] = path[dis + 1];
     ans2[j] = path[n - dis];
    }
    cout << "!";
    for(int i = 1; i <= n; i++){
     cout << " " << ans1[i];
    }
    for(int i = 1; i <= n; i++){
  cout << " " << ans2[i];
    }
    cout << endl;
    cin >> n;
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