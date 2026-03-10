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
    int n, m;
    cin >> n >> m;
    set<int> occupied;
    queue<pair<int,int>> q;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        occupied.insert(x);
        q.push({x + 1, 1});
        q.push({x - 1, 1});
    }
    vector<int> pos;
    int distance_sum = 0;
    pos.reserve(m);
    while(!q.empty() and m){
        auto [x, d] = q.front();
        q.pop();
        if(occupied.count(x))
            continue;
        m--;
        distance_sum += d;
        pos.push_back(x);
        occupied.insert(x);
        q.push({x + 1, d + 1});
        q.push({x - 1, d + 1});
    }
    cout << distance_sum << endl;
    for(auto &x: pos)
        cout << x << " ";
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