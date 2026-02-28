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
    deque<deque<int>> grid;
    set<deque<int>> processed;
    for(int i = 0; i < n; i++){
        int m;
        cin >> m;
        deque<int> tmp(m), v;
        set<int> present;
        for(int j = 0; j < m; j++)
            cin >> tmp[j];
        for(int j = m - 1; j >= 0; j--){
            if(present.count(tmp[j]))
                continue;
            else{
                v.push_back(tmp[j]);
                present.insert(tmp[j]);
            }
        }
        if(processed.count(v) == 0)
            grid.push_back(v);
    }
    sort(all(grid));
    set<int> present;
    vector<int>ans;
    while(!grid.empty()){
        while(sz(grid) and sz(grid.front()) == 0)
            grid.pop_front();
        if(sz(grid) == 0)
            break;
        sort(all(grid),[&](deque<int>&a, deque<int>&b){
            while(sz(a) and present.count(a[0]))
                a.pop_front();
            while(sz(b) and present.count(b[0]))
                b.pop_front();
            if(a.empty() or b.empty())
                return sz(a) < sz(b);
            return a[0] < b[0];
        });
        while(sz(grid) > 1 and sz(grid[0]) and sz(grid[1]) and grid[0][0] == grid[1][0]){
            if(present.count(grid[0][0]) == 0){
                ans.push_back(grid[0][0]);
                present.insert(ans.back());
            }
            int i = 0;
            for (i; i < sz(grid) and sz(grid[i]) and grid[i][0] == ans.back(); i++){
                grid[i].pop_front();
            }
            sort(grid.begin(), grid.begin() + i, [&](deque<int> &a, deque<int> &b)
                 {
            while(sz(a) and present.count(a[0]))
                a.pop_front();
            while(sz(b) and present.count(b[0]))
                b.pop_front();
            if(a.empty() or b.empty())
                return sz(a) < sz(b);
            return a[0] < b[0]; });
        }
        for(auto &x: grid.front())
            if(present.count(x) == 0){
                ans.push_back(x);
                present.insert(x);
            }
        grid.pop_front();
    }
    for(auto &x: ans)
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}