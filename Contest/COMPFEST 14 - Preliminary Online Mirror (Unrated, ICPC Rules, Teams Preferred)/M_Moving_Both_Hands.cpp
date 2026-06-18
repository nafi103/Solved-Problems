#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl '\n'
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int n, m;
    cin >> n >> m;
    vector<vector<int>> dis(n, vector<int>(2, inf));
    vector<vector<vector<pair<int,int>>>> g(2, vector<vector<pair<int,int>>>(n));
    for(int i = 0, u, v, w; i < m; i++){
        cin >> u >> v >> w;
        u--, v--, w;
        g[0][u].emplace_back(v, w);
        g[1][v].emplace_back(u, w);
    }
    dis[0][0] = 0;
    using tup = array<int, 3>;
    priority_queue<tup, vector<tup>, greater<tup>> q;
    q.push({0, 0, 0}); // d, node, t
    while(!q.empty()){
        auto [d, node, t] = q.top();
        q.pop();
        if(d > dis[node][t])
            continue;
        for(auto &[nbr, w]: g[t][node]){
            if(dis[nbr][t] > d + w){
                dis[nbr][t] = d + w;
                q.push({dis[nbr][t], nbr, t});
            }
        }
        if(t == 0){
            for(auto &[nbr, w]: g[1][node]){
                if(dis[nbr][1] > d + w){
                    dis[nbr][1] = d + w;
                    q.push({dis[nbr][1], nbr, 1});
                }
            }
        }
    }
    for(int i = 1, d; i < n; i++){
        d = min(dis[i][0], dis[i][1]);
        if(d == inf){
            cout << -1;
        }else{
            cout << d;
        }
        cout << (i == n - 1 ? endl : ' ');
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}