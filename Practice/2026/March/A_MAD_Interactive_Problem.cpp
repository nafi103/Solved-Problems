#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int query(vector<int> &q){
    cout << "? " << sz(q);
    for(auto &x: q){
        cout << " " << x;
    }
    cout << endl;
    int val;
    cin >> val;
    return val;
}

void solve()
{
    int n;
    cin >> n;
    vector<int> q = {1}, arr(2 * n + 1, 0);
    for(int i = 2; i <= 2 * n; i++){
        q.push_back(i);
        int value = query(q);
        if(value){
            arr[i] = value;
            q.pop_back();
        }
    }
    q.clear();
    for(int i = 2 * n; i >= 1; i--){
        q.push_back(i);
        if(arr[i] == 0){
            arr[i] = query(q);
            q.pop_back();
        }
    }
    cout << "! ";
    for(int i = 1; i <= 2 * n; i++){
        cout << arr[i] << " " ;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}