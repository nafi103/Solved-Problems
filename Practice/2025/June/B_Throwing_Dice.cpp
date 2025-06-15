#include<bits/stdc++.h>
using namespace std;

#define int long long

const int N = 26, X = 151;
pair<int,int> dummy = {-1,-1}, zero = {0,0}, one = {1,1};

vector<vector<pair<int,int>>>dp(N, vector<pair<int,int>>(X, dummy));

pair<int,int> operator+(const pair<int,int>&a, const pair<int,int>&b){
	if(a==zero) return b;
	if(b==zero) return a;
	int denom = lcm(a.second, b.second);
	int x = denom/a.second, y = denom/b.second;
	int nom = x*a.first + y*b.first;
	int g = gcd(nom,denom);
	nom/=g;
	denom/=g;
	return {nom,denom};
}

pair<int,int> operator*(const pair<int,int>&a, const pair<int,int>&b){
	if(a==zero or b == zero) return zero;
	int denom = a.second*b.second;
	int nom = a.first*b.first;
	int g = gcd(nom,denom);
	nom/=g;
	denom/=g;
	return {nom,denom};
}

pair<int,int> f(int n, int x){
	if(n>=x)
		return {1,1};
	if(n*6<x)
		return {0,0};
	pair<int,int> &ans = dp[n][x];
	if(ans != dummy)
		return ans;
	ans = zero;
	for(int i = 1; i<7; i++){
		ans = ans + (make_pair(1,6)*f(n-1,x-i));
	}
	return ans;
}

void solve(){
	int n,x;
    cin>>n>>x;
	pair<int,int>ans = f(n,x);
    if(ans== zero ){
        cout<<0<<endl;
        return;
    }
    if (ans == one){
        cout<<1<<endl;
        return;
    }
	cout<<ans.first<<"/"<<ans.second<<endl;
}

int32_t main(){
	int t;
	cin>>t;
    int cnt = 1;
	while(t--){
        cout << "Case "<<cnt++<<": ";
		solve();
	}
} 