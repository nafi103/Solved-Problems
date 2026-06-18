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
 vector<vector<int>>t,parents;
vector<int>level; 
int mx, n, q;
 void dfs(int node, int parent, int cLevel){
    level[node] = cLevel;
    parents[0][node] = parent;
    for(auto &x: t[node]){
        if(x!=parent) dfs(x,node, cLevel+1);
    }
}
 int kthParent(int a, int k){
    for(int i = 0; i<mx; i++){
        if(a == -1) return a;
        if(k&(1<<i)) a = parents[i][a];
    }
    return a;
}
 int lca(int a, int b){
    if(level[a]>level[b]){
        a = kthParent(a, level[a] - level[b]);
    }else{
        b = kthParent(b, level[b] - level[a]);
    }
    if(a==b) return a;
    for(int i = mx - 1; i>=0; i--){
        if(parents[i][a]!=parents[i][b]){
            a = parents[i][a];
            b = parents[i][b];
        }
    }
    return parents[0][a];
}
 int distance(int a,int b){
    return level[a] + level[b] - 2*level[lca(a,b)];
}
 void input(){
    cin >> n >> q;
    mx = log2(n) + 5;
    t.resize(n);
    level.resize(n);
    parents.assign(mx, vector<int>(n, -1));
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--,v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}
 void solve()
{
    input();
    dfs(0, -1, 0);
    for(int i = 1; i < mx; i++){
        for(int node = 0; node < n; node++){
            int prev = parents[i - 1][node];
            if(prev != -1)
                parents[i][node] = parents[i - 1][prev];
        }
    }
    while(q--){
        int k;
        cin >> k;
        vector<int> arr(k);
        for(auto &x: arr){
            cin >> x;
            x--;
        }
        sort(all(arr), [&](int &a, int &b){
            return level[a] < level[b];
        });
        int l = arr[k - 1];
        bool flag = true;
        for(int i = k - 2; i >= 0; i--){
            int newL = lca(l, arr[i]);
            if(newL != arr[i]){
                if(distance(newL, arr[i]) > 1){
                    flag = false;
                    break;
                }
            }
            l = newL;
        }
        cout << (flag ? "YES" : "NO") << endl;
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