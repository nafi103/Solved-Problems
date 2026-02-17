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

set<pair<int,int>> edges;

int get_pathLen(int k){
    cout << "? " << k << endl;
    int path_len, tmp;
    cin >> path_len;
    if(path_len == 0)
        return 0;
    vector<int> path(path_len);
    for(int i = 0; i < path_len; i++)
        cin >> path[i];
    for(int i = 0; i < path_len - 1; i++){
        edges.insert({path[i], path[i + 1]});
    }
    return path_len;
}

pair<int,int> get_firstTwo(int k){
    cout << "? " << k << endl;
    int path_len, tmp, a, b;
    cin >> path_len;
    vector<int> path(path_len);
    for(int i = 0; i < path_len; i++)
        cin >> path[i];
    for(int i = 0; i < path_len - 1; i++){
        edges.insert({path[i], path[i + 1]});
    }
    if(path_len == 1){
        return {path[0], -inf};
    }
    return {path[0], path[1]};
}

int find_paths(int l, int r){
    if(l > r)
        return r;
    int mid = (l + r) / 2;
    if(get_pathLen(mid) > 0)
        return find_paths(mid + 1, r);
    return find_paths(l, mid - 1);
}

void solve()
{
    edges.clear();
    int n;
    cin >> n;
    int paths = find_paths(1, (1 << 30)), l = 2;
    if(paths == 0){
        cout << "! 0" << endl;
        return;
    }
    for(int u = 1; u <= n; u++){
        for(int v = 1; v <= n; v++){
            if(u == v or edges.count({u, v}) or edges.count({v, u}))
                continue;
            int r = paths;
            while(l <= r){
                int mid = (l + r) / 2;
                pair<int,int> my = {u , v}, got = get_firstTwo(mid);
                if(edges.count(my))
                    break;
                if(my == got){
                    edges.insert({u , v});
                    l = r = mid;
                    break;
                }else if(got > my){
                    r = mid - 1;
                }else{
                    l = mid + 1;
                }
            }
            if(l + 1 <= paths){
                auto [a, b] = get_firstTwo(l + 1);
                if(a != u){
                    u = a - 1;
                    break;
                }else if(v + 1 < b){
                    v = b - 1;
                }
            }
        }
    }
    cout << "! " << sz(edges) << endl;
    for(auto &[f, s]: edges)
        cout << f << " " << s << endl;
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