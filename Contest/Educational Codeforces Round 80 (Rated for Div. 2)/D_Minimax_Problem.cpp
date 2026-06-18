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
int n, m, mx = -inf;
vector<vector<int>> grid;
vector<pair<int,int>> possible;
pair<int,int> target_value;
 int get_value(vector<int> &arr, int target){
    int res = 0;
    for(int j = 0; j < m; j++)
        if(arr[j] >= target)
            res |= (1 << j);
    return res;
}
 bool check(int target){
    vector<bool> visited((1 << m), 0);
    for(int i = 0; i < n; i++){
        visited[get_value(grid[i], target)] = true;
    }
     for(auto &[l, r]: possible){
        if(visited[l] and visited[r]){
            target_value = {l, r};
            return true;
        }
    }
     return false;
}
 void solve()
{
    cin >> n >> m;
    grid.resize(n, vector<int> (m));
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            cin >> grid[i][j];
            mx = max(mx, grid[i][j]);
        }
    }
     int R = 1 << m, target = (1 << m) - 1;
    for(int i = 0; i < R; i++){
        for(int j = i; j < R; j++){
            if((i | j) == target){
                possible.push_back({i, j});
            }
        }
    }
     int l = 0, r = mx;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(mid))
            l = mid + 1;
        else
            r = mid - 1;
    }
     for(int i = 0; i < n; i++){
        if(get_value(grid[i], r) == target_value.first){
            cout << i + 1 << " ";
            break;
        }
    }
     for(int i = 0; i < n; i++){
        if(get_value(grid[i], r) == target_value.second){
            cout << i + 1 << endl;
            break;
        }
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