#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int k,n, p = 1,i,cnt = 1;
        cin>>k>>n;
        vector<int>arr(n+1,0);
        arr[1]=1;
        for (i = 1; i<= k+1; i++)
        {
            if(p>n||i==k) break;
            if(i+p<=n){
                arr[i+p]=1;
                cnt++;
                p+=i;
            }
        }
        for (i = n; i >=1; i--)
        {
            if(cnt==k) break;
            if(arr[i]==0){
                arr[i]=1;
                cnt++;
            }
        }
        for (int j = 1; j <= n;j++){
            if(arr[j]==1)   cout<<j<<" ";
        }
        cout<<endl;
    }
}