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
    cin >> n >> m;
    vector<bitset<2010>> pre(m), curr(m);
    for(int i = 0; i < m; i++){
    	pre[i].reset();
    }
    pre[0][1005] = 1;
    for(int i = 0; i < n; i++){
    	for(int j = 0; j < m; j++){
    		int x;
    		cin>>x;
			if(x==1){
    			curr[j] = (pre[j] << 1);
    		}else{
    			curr[j] = (pre[j] >> 1);
    		}
    		if(j){
    			if(x==1){
	    			curr[j] |= (curr[j-1] << 1);
	    		}else{
	    			curr[j] |= (curr[j-1] >> 1);
	    		}
    		}
    	}
    	pre = curr;
    }
    if(curr[m-1][1005]){
    	cout<<"YES"<<endl;
    }else{
    	cout<<"NO"<<endl;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}