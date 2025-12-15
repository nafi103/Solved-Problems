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

bool check(vector<int> &pref, vector<pair<int,int>> &intervals){
	set<int> s;
	for(auto &[l,r]: intervals){
		if(pref[r] - pref[l - 1] == 1)
			return false;
	}
	return true;
}

void solve()
{
    int n, m;
    cin >> n >> m;
    vector<pair<int,int>> interval(m);
    vector<int> range(n + 2, 0);
    for(auto &[l,r] : interval){
    	cin >> l >> r;
    	range[l]++;
    	range[r+1]--;
    }
    for(int i = 1; i <= n; i++){
    	range[i] += range[i-1];
    	if(range[i] == m){
    		for(int j = 1, p = 1; j <= n; j++, p++){
    			if(j == i){
    				cout << 0 << " ";
    				p--;
    			}else{
    				cout << p << " ";
    			}
    		}
    		cout << endl;
    		return;
    	}
    }
    for(int i = 1; i<=n; i++){
    	fill(all(range), 0);
    	range[i] = 1;
    	if(i > 1){
    		range[i - 1] = 2;
    		for(int j = i; j <=n; j++){
    			range[j] += range[j - 1];
    		}
    		if(check(range, interval)){
    			int p = 2;
    			vector<int> ans(n + 1, -1);
    			ans[i] = 0;
    			ans[i - 1] = 1;
    			for(int j = 1; j <= n; j++){
    				if(ans[j] == -1)
    					ans[j] = p++;
    			}
    			for(int i = 1; i <= n; i++)
    				cout << ans[i] << " ";
    			cout<< endl;
    			return;
    		}
    	}
    	fill(all(range), 0);
    	range[i] = 1;
    	if(i < n){
    		range[i + 1] = 2;
    		for(int j = i; j <= n; j++){
    			range[j] += range[j - 1];
    		}
    		if(check(range, interval)){
    			int p = 2;
    			vector<int> ans(n + 1, -1);
    			ans[i] = 0;
    			ans[i + 1] = 1;
    			for(int j = 1; j <= n; j++){
    				if(ans[j] == -1)
    					ans[j] = p++;
    			}
    			for(int i = 1; i <= n; i++)
    				cout << ans[i] << " ";
    			cout << endl;
    			return;
    		}
    	}
    }
    for(int i = 1; i <= n; i++){
    	if(i == 1)
    		cout << 0 << " ";
    	else if(i == n)
    		cout << 1 << " ";
    	else
    		cout << i << " ";
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