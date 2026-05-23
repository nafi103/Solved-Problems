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
int h[N], n, m, k, in_degree[N], dp[N];
vector<int> g[N];

void input(){
    cin >> n >> m >> k;
    for(int i = 0; i < n; i++){
        g[i].clear();
        in_degree[i] = 0;
    }

    for(int i = 0; i < n; i++)
        cin >> h[i];

    for(int i = 0, u, v; i < m; i++){
        cin >> u >> v;
        u--, v--;

        in_degree[v]++;
        g[u].push_back(v);
    }
}

void solve()
{
    input();

    vector<int> topo, saved;
    queue<int> q;
    for(int i = 0; i < n; i++){
        if(in_degree[i] == 0){
            q.push(i);
            saved.push_back(i);
        }
    }

    while(!q.empty()){
        int node = q.front();
        q.pop();
        topo.push_back(node);
        for(auto &adj: g[node]){
            in_degree[adj]--;
            if(in_degree[adj] == 0)
                q.push(adj);
        }
    }

    for(int i = n - 1; i >= 0; i--){
        int &node = topo[i];
        int mx = 0;
        for(auto &adj: g[node]){
            mx = max(mx, (h[adj] - h[node] + k) % k + dp[adj]);
        }
        dp[node] = mx;
    }

    vector<pair<int,int>> ranges;
    for(auto &node: saved){
        ranges.push_back({h[node], h[node] + dp[node]});
    }

    sort(all(ranges));
    int max_end = 0;
    for(auto &range : ranges){
        max_end = max(max_end, range.second);
    }
    int ans = inf;
    for(int i = 0; i < sz(ranges); i++){
        ans = min(ans, max_end - ranges[i].first);
        max_end = max(max_end, ranges[i].second + k);
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