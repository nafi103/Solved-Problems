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
    int n, m, cnt;
    cin >> n >> m;
     vector<set<int>> block(n);
    while(m--){
        int u, v;
        cin >> u >> v;
        u--, v--;
        block[u].insert(v);
        block[v].insert(u);
    }
     vector<int> cc;
    set<int> unvisited;
    for(int i = 0; i < n; i++)
        unvisited.insert(i);
    for(int i = 0; i < n; i++){
        if(unvisited.count(i)){
            cnt = 0;
             queue<int> q;
            q.push(i);
            unvisited.erase(i);
             while(!q.empty()){
                int node = q.front();
                cnt++;
                q.pop();
                 vector<int> ers;
                for(auto &adj: unvisited){
                    if(!block[node].count(adj)){
                        ers.push_back(adj);
                        q.push(adj);
                    }
                }
                 for(auto &x: ers)
                    unvisited.erase(x);
            }
             cc.push_back(cnt);
        }
    }
     sort(all(cc));
    cout << sz(cc) << endl;
    for(auto &x: cc){
        cout << x << " ";
    }
    cout << endl;
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
