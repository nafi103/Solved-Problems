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
 const int N = 2e5;
vector<int> g[N], rg[N];
int d[N], n, dp[N][2];
 void input(){
    int m;
    cin >> n >> m;
    for(int i = 0; i < n; i++){
        g[i].clear();
        rg[i].clear();
        dp[i][0] = dp[i][1] = inf;
        d[i] = inf;
    }
     for(int i = 0, u, v; i < m; i++){
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        rg[v].push_back(u);
    }
}
 void get_distance(){
    queue<int> q;
    d[0] = 0;
    q.push(0);
     while(!q.empty()){
        int node = q.front();
        q.pop();
         for(auto &adj: g[node]){
            if(d[adj] > d[node] + 1){
                d[adj] = d[node] + 1;
                dp[adj][0] = d[adj];
                q.push(adj);
            }
        }
    }
}
 void solve()
{
    input();
    get_distance();
     // for(int i = 0; i < n; i++){
    //     debug(rg[i])
    //     cerr << d[i] << " \n"[i == n - 1];
    // }
     dp[0][0] = dp[0][1] = 0;
    using tup = array<int, 3>;
    priority_queue<tup, vector<tup>, greater<tup>> q; // distance, node, used
    for(int i = 0; i < n; i++){
        q.push({dp[i][0], i, 0});
    }
     while(!q.empty()){
        auto [D, node, used] = q.top();
        q.pop();
         if(D > dp[node][used])
            continue;
         for(auto &adj: rg[node]){
            if(!used){
                if(d[adj] < d[node]){
                    if(dp[adj][0] > D){
                        dp[adj][0] = D;
                        q.push({D, adj, 0});
                    }
                }else{
                    if(dp[adj][1] > D){
                        dp[adj][1] = D;
                        q.push({D, adj, 1});
                    }
                }
            }else{
                if(d[adj] < d[node]){
                    if(dp[adj][1] > D){
                        dp[adj][1] = D;
                        q.push({D, adj, 1});
                    }
                }
            }
        }
    }
     for(int i = 0; i < n; i++){
        cout << min(dp[i][0], dp[i][1]) << " \n"[i == n - 1];
    }
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