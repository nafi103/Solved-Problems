#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int n, k, x, a, b, c;
    cin >> n >> k >> x >> a >> b >> c;
    int arr[n];
    arr[0] = x;
    deque<int> dq;
    dq.push_back(0);
    int xr = 0;
    if(k == 1)
        xr = x;
    for(int i = 1; i < n; i++){
        arr[i] = (1ll * arr[i - 1] * a + b) % c;
        while(!dq.empty() and arr[dq.back()] > arr[i])
            dq.pop_back();
        dq.push_back(i);
        if(dq.front() <= i - k)
            dq.pop_front();
        if(i >= k - 1){
            xr = xr ^ (arr[dq.front()]);
        }
    }
    cout << xr << endl;
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