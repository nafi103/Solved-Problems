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

void solve()
{
    int n,m;
    cin>>n>>m;
    vector<int> v(n), blocks;
    for(auto &x: v)
    	cin>>x;
    int cnt = 1;
    for(int i = 1; i < n; i++){
    	if(v[i]!=v[i-1]){
    		blocks.push_back(cnt);
    		cnt = 1;
    	}else{
    		cnt++;
    	}
    }
    blocks.push_back(cnt);
    int ans = 0, pre = 0, len = 0;
    for(auto &x: blocks){
    	pre += len;
    	ans += (x*(x+1))/2;
    	ans += pre*x;
    	len += x;
    	pre += x;
    }
    while(m--){
    	int i,x;
    	cin >> i >> x;
    	i--;
    	if(i){
    		int prev = (v[i] == v[i-1]), curr = (v[i-1] == x);
    		if(prev != curr){
    			int add = (prev > curr ? 1 : -1);
    			ans += (i * (n - i) * add);
    		}
    	}
    	if(i < n - 1){
			int prev = (v[i] == v[i + 1]), curr = (v[i + 1] == x);
    		if(prev != curr){
    			int add = (prev > curr ? 1 : -1);
    			ans += ((i + 1) * (n - i - 1) * add);
    		}
    	}
    	v[i] = x;
    	cout << ans << endl;
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
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}