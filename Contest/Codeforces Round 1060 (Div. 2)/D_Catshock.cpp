#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<set<int>> t;
vector<int> parent, level;

struct Operation{
    int t, id;
    Operation(){
        t = 1, id = 0;
    }
    Operation(int _id){
        t = 2, id = _id;
    }
    void write(){
        if(t==1)
            cout << 1 << endl;
        else
            cout << 2 << " " << id << endl;
    }
};

void dfs(int node, int l, int par)
{
    parent[node] = par;
    level[node] = l;
    for (auto &child : t[node])
    {
        if (child != par)
        {
            dfs(child, l + 1, node);
        }
    }
}

void solve()
{
    level.clear();
    t.clear();
    parent.clear();
    int n;
    cin >> n;
    level.resize(n + 1);
    t.resize(n + 1);
    parent.resize(n + 1);
    for (int i = 1; i < n; i++)
    {
        int u, v;
        cin >> u >> v;
        t[u].insert(v);
        t[v].insert(u);
    }
    dfs(n, 0, -1);
    if(level[1]&1){
        for (int i = 1; i <= n; i++){
            level[i]++;
        }
    }
    vector<Operation> op;
    vector<int> degree(n + 1);
    vector<int> even, odd;
    for (int i = 1; i < n; i++)
    {
        degree[i] = sz(t[i]);
        if (degree[i] == 1)
        {
            if (level[i] & 1)
                odd.push_back(i);
            else
                even.push_back(i);
        }
    }
    int d = 0, rem = n-1;
    while(!(even.empty() and odd.empty())){
        if(d&1){
            d++;
            if(even.empty()){
                op.push_back(Operation());
                continue;
            }
            int node = even.back(), p = parent[node];
            even.pop_back();
            op.push_back(Operation(node));
            if(p==-1){
                op.push_back(Operation());
                continue;
            }
            degree[p]--;
            if (degree[p]==1 and p!=n){
                if(level[p]&1)
                    odd.push_back(p);
                else
                    even.push_back(p);
            }
        }else{
            d++;
            if (odd.empty())
            {
                op.push_back(Operation());
                continue;
            }
            int node = odd.back(), p = parent[node];
            odd.pop_back();
            op.push_back(Operation(node));
            if (p == -1){
                op.push_back(Operation());
                continue;
            }
            degree[p]--;
            if (degree[p] == 1 and p!=n)
            {
                if (level[p] & 1)
                    odd.push_back(p);
                else
                    even.push_back(p);
            }
        }
        op.push_back(Operation());
    }
    cout << sz(op) << endl;
    for(auto &x: op)
        x.write();
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}