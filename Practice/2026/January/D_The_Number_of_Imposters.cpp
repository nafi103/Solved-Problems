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
int node_count, n, m, u, v, color[N];
vector<vector<pair<int,bool>>> g(N);
string col;

void input(){
    cin >> n >> m;
    for(int i = 1; i <= n; i++){
        color[i] = -1;
        g[i].clear();
    }
    while(m--){
        cin >> u >> v >> col;
        bool c = col == "imposter";
        g[u].emplace_back(v, c);
        g[v].emplace_back(u, c);
    }
}

int dfs(int node, bool c){
    int ans = c; color[node] = c; node_count++;
    for(auto &[nbr, nc]: g[node]){
        if(color[nbr] == -1){
            ans += dfs(nbr, nc ^ c);
        }else if((c and nc == color[nbr]) or (!c and (nc != color[nbr])))
            return -inf;
    }
    return ans;
}


void solve()
{
    input();
    int ans = 0;
    for(int i = 1; i <= n; i++){
        if(color[i] == -1){
            node_count = 0;
            int tmp = dfs(i, 1);
            if(tmp < 0){
                cout << -1 << endl;
                return;
            }
            ans += max(tmp, node_count - tmp);
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