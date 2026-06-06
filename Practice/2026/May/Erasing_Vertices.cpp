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

void solve()
{
    int n;
    cin >> n;

    vector<bool> visited(n);
    vector<vector<int>> g(n);
    for(int u = 0; u < n; u++){
        for(int v = 0; v < n; v++){
            char e;
            cin >> e;
            if(e == '1')
                g[u].push_back(v);
        }
    }

    vector<int> reach(n);
    for(int i = 0; i < n; i++){
        fill(all(visited), false);
        queue<int> q;
        q.push(i);
        visited[i] = true;

        while(!q.empty()){
            int node = q.front();
            q.pop();

            for(auto &adj: g[node]){
                if(!visited[adj]){
                    reach[adj]++;
                    visited[adj] = true;
                    q.push(adj);
                }
            }
        }
    }

    double ev = 0;
    for(auto &x: reach){
        ev += (1.0 / (x + 1));
    }

    cout << ev << endl;
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